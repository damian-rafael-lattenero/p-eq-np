module PeqNP.Interference
  ( -- * Complex generating function with interference
    ComplexVal(..)
  , cMul
  , cAdd
  , cAbs2
  , cFromPolar
    -- * Interference-based coefficient extraction
  , evalGeneratingComplex
  , interferenceExtract
  , InterferenceResult(..)
  , showInterferenceResult
    -- * Scaling analysis
  , interferenceScaling
  , showInterferenceScaling
  ) where

import qualified Data.Set as Set

import PeqNP.DPSolver (dpReachable)

-- | Complex number (real, imaginary) — no external deps needed
data ComplexVal = CV !Double !Double
  deriving (Show)

cMul :: ComplexVal -> ComplexVal -> ComplexVal
cMul (CV a b) (CV c d) = CV (a*c - b*d) (a*d + b*c)

cAdd :: ComplexVal -> ComplexVal -> ComplexVal
cAdd (CV a b) (CV c d) = CV (a+c) (b+d)

cAbs2 :: ComplexVal -> Double
cAbs2 (CV a b) = a*a + b*b

cFromPolar :: Double -> Double -> ComplexVal
cFromPolar r theta = CV (r * cos theta) (r * sin theta)

cScale :: Double -> ComplexVal -> ComplexVal
cScale s (CV a b) = CV (s*a) (s*b)

cZero :: ComplexVal
cZero = CV 0 0

cOne :: ComplexVal
cOne = CV 1 0

-- ═══════════════════════════════════════════════════════════
-- Core: evaluate g(x) = Π(1 + x^wᵢ) at a complex point
-- ═══════════════════════════════════════════════════════════

-- | Evaluate g(α) = Π(1 + α^wᵢ) at a complex point α.
-- This is O(n) — one multiplication per weight.
-- The KEY: this is the generating function with INTERFERENCE.
-- At roots of unity ω = e^{2πi/q}, the evaluation captures
-- the DFT of the coefficient sequence.
evalGeneratingComplex :: ComplexVal -> [Int] -> ComplexVal
evalGeneratingComplex alpha weights = foldl step cOne weights
  where
    step acc w = acc `cMul` (cOne `cAdd` complexPow alpha w)

-- | Complex exponentiation by repeated squaring
complexPow :: ComplexVal -> Int -> ComplexVal
complexPow _ 0 = cOne
complexPow base 1 = base
complexPow base n
  | even n    = let half = complexPow base (n `div` 2) in half `cMul` half
  | otherwise = base `cMul` complexPow base (n - 1)

-- ═══════════════════════════════════════════════════════════
-- Interference-based coefficient extraction
-- ═══════════════════════════════════════════════════════════

-- | Extract [x^T] g(x) using interference.
--
-- THE METHOD:
-- [x^T] g(x) = (1/q) Σ_{j=0}^{q-1} g(ω^j) · ω^{-jT}
-- where ω = e^{2πi/q} is a primitive q-th root of unity.
--
-- With q evaluations: EXACT if q > degree(g) = Σwᵢ.
-- With q < degree(g): APPROXIMATE due to aliasing (wraparound).
--
-- THE INTERFERENCE:
-- Each evaluation g(ω^j) mixes contributions from ALL coefficients.
-- When we multiply by ω^{-jT} and SUM over j, terms at position T
-- add CONSTRUCTIVELY (all phases align), while terms at other
-- positions add DESTRUCTIVELY (phases cancel by symmetry).
--
-- With q points: perfect cancellation for positions that differ
-- from T by a multiple of q. False positives from aliasing.
--
-- THE QUESTION: how small can q be while still distinguishing T?
-- If q can be poly(n) → polynomial time extraction → P = NP.

data InterferenceResult = IR
  { irWeights       :: [Int]
  , irTarget        :: Int
  , irQ             :: Int       -- number of evaluation points
  , irCoeffEstimate :: Double    -- estimated [x^T] coefficient
  , irIsNonzero     :: Bool      -- estimate > threshold?
  , irCorrect       :: Bool      -- agrees with DP?
  , irAmplification :: Double    -- signal-to-noise ratio
  , irPhaseValues   :: [Double]  -- |g(ω^j)| for each j (for analysis)
  } deriving (Show)

interferenceExtract :: Int -> [Int] -> Int -> InterferenceResult
interferenceExtract q weights target =
  let -- ω = e^{2πi/q}
      omega j = cFromPolar 1.0 (2 * pi * fromIntegral j / fromIntegral q)
      -- Evaluate g(ω^j) for j = 0..q-1
      evaluations = [evalGeneratingComplex (omega j) weights | j <- [0..q-1]]
      -- Phase factor: ω^{-jT}
      phaseFactors = [cFromPolar 1.0 (-2 * pi * fromIntegral (j * target) / fromIntegral q) | j <- [0..q-1]]
      -- Inverse DFT: [x^T] ≈ (1/q) Σ g(ω^j) · ω^{-jT}
      summed = foldl cAdd cZero (zipWith cMul evaluations phaseFactors)
      coeffEstimate = cAbs2 summed / fromIntegral (q * q)  -- |[x^T]|² approximation
      -- The actual coefficient magnitude
      coeffMag = sqrt coeffEstimate
      -- Threshold: if coeffMag > 0.5, likely nonzero
      isNonzero = coeffMag > 0.5
      -- Ground truth
      dpAnswer = Set.member target (dpReachable weights)
      -- Phase magnitudes (for analysis)
      phaseMags = map (\e -> sqrt (cAbs2 e)) evaluations
      -- Signal-to-noise: |coefficient at T| / mean |coefficient at other positions|
      amplification = if coeffMag > 0.001 then coeffMag else 0
  in IR
    { irWeights       = weights
    , irTarget        = target
    , irQ             = q
    , irCoeffEstimate = coeffMag
    , irIsNonzero     = isNonzero
    , irCorrect       = isNonzero == dpAnswer
    , irAmplification = amplification
    , irPhaseValues   = take 10 phaseMags  -- first 10 for display
    }

showInterferenceResult :: InterferenceResult -> String
showInterferenceResult ir = unlines
  [ "  q=" ++ show (irQ ir) ++ " target=" ++ show (irTarget ir)
  , "  Coeff estimate: " ++ show (roundTo 4 (irCoeffEstimate ir))
  , "  Nonzero: " ++ show (irIsNonzero ir) ++ "  Correct: " ++ show (irCorrect ir)
  , "  Amplification: " ++ show (roundTo 4 (irAmplification ir))
  , "  |g(ω^j)| first 10: " ++ show (map (roundTo 2) (irPhaseValues ir))
  ]
  where roundTo n x = fromIntegral (round (x * 10^(n::Int)) :: Int) / 10^(n::Int)

-- ═══════════════════════════════════════════════════════════
-- Scaling: how does interference work vs q?
-- ═══════════════════════════════════════════════════════════

interferenceScaling :: [Int] -> Int -> [Int] -> [InterferenceResult]
interferenceScaling weights target qValues =
  [interferenceExtract q weights target | q <- qValues]

showInterferenceScaling :: [InterferenceResult] -> String
showInterferenceScaling results = unlines $
  [ "  " ++ padR 6 "q" ++ padR 10 "coeff" ++ padR 8 "nonz" ++ padR 8 "corr"
    ++ "work=O(n×q)"
  , "  " ++ replicate 45 '-'
  ] ++
  [ "  " ++ padR 6 (show (irQ r))
    ++ padR 10 (show (roundTo 3 (irCoeffEstimate r)))
    ++ padR 8 (show (irIsNonzero r))
    ++ padR 8 (show (irCorrect r))
    ++ show (length (irWeights r) * irQ r)
  | r <- results
  ]
  where
    padR n s = s ++ replicate (max 0 (n - length s)) ' '
    roundTo n x = fromIntegral (round (x * 10^(n::Int)) :: Int) / 10^(n::Int)
