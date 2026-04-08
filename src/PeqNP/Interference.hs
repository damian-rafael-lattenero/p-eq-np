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
    -- * CRT multi-prime interference
  , multiPrimeTest
  , MultiPrimeResult(..)
  , showMultiPrimeResult
    -- * Kuperberg + interference pipeline
  , kuperbergThenInterference
  , PipelineIntResult(..)
  , showPipelineIntResult
  ) where

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Bits ((.&.))

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

-- ═══════════════════════════════════════════════════════════
-- CRT MULTI-PRIME INTERFERENCE
-- ═══════════════════════════════════════════════════════════

-- | Multi-prime interference: use MULTIPLE small primes q₁, q₂, ...
-- and combine results via CRT logic.
--
-- For each prime qᵢ, compute [x^T] g(x) mod aliasing at qᵢ.
-- A TRUE nonzero coefficient is nonzero in ALL DFTs.
-- A FALSE positive (aliased nonzero) at prime qᵢ has probability ≈ D/qᵢ
-- where D = number of nonzero coefficients at positions ≡ T mod qᵢ.
--
-- With k independent primes: P(all give false positive) ≈ Π(Dᵢ/qᵢ).
-- If Π qᵢ > total number of coefficients → P(false positive) < 1 → EXACT.
--
-- COST: O(n × Σ qᵢ). With k = O(log n) primes of size O(n) each:
-- O(n × n × log n) = O(n² log n). For density 1: DP = O(n × 2ⁿ).
-- If this works → O(n² log n) << O(n × 2ⁿ) → POLYNOMIAL!

data MultiPrimeResult = MPR
  { mprWeights      :: [Int]
  , mprTarget       :: Int
  , mprPrimes       :: [Int]       -- primes used
  , mprCoeffs       :: [Double]    -- coefficient estimate per prime
  , mprAllNonzero   :: Bool        -- ALL primes say nonzero?
  , mprAnyZero      :: Bool        -- ANY prime says zero?
  , mprVerdict      :: Bool        -- our answer: allNonzero
  , mprCorrect      :: Bool        -- agrees with DP?
  , mprTotalWork    :: Int         -- n × Σ qᵢ
  , mprDPWork       :: Int         -- DP distinct sums
  } deriving (Show)

multiPrimeTest :: [Int] -> Int -> [Int] -> MultiPrimeResult
multiPrimeTest weights target primes =
  let results = [interferenceExtract q weights target | q <- primes]
      coeffs = map irCoeffEstimate results
      -- A coefficient is "nonzero" if estimate > 0.5
      nonzeros = map (> 0.5) coeffs
      allNZ = and nonzeros
      anyZ = any not nonzeros
      -- Verdict: say YES only if ALL primes agree it's nonzero
      -- (conservative: if ANY says zero, we say NO)
      verdict = allNZ
      -- Ground truth
      dpAnswer = Set.member target (dpReachable weights)
      n = length weights
      totalWork = n * sum primes
      dpWork = Set.size (dpReachable weights)
  in MPR
    { mprWeights    = weights
    , mprTarget     = target
    , mprPrimes     = primes
    , mprCoeffs     = coeffs
    , mprAllNonzero = allNZ
    , mprAnyZero    = anyZ
    , mprVerdict    = verdict
    , mprCorrect    = verdict == dpAnswer
    , mprTotalWork  = totalWork
    , mprDPWork     = dpWork
    }

showMultiPrimeResult :: MultiPrimeResult -> String
showMultiPrimeResult mpr = unlines
  [ "  Primes: " ++ show (mprPrimes mpr)
  , "  Coefficients: " ++ show (map (roundTo 2) (mprCoeffs mpr))
  , "  Per-prime nonzero: " ++ show (map (> 0.5) (mprCoeffs mpr))
  , "  Verdict: " ++ (if mprVerdict mpr then "YES" else "NO")
      ++ "  Correct: " ++ show (mprCorrect mpr)
  , "  Work: " ++ show (mprTotalWork mpr) ++ " (DP: " ++ show (mprDPWork mpr) ++ ")"
  , "  Speedup: " ++ show (roundTo 1 (fromIntegral (mprDPWork mpr) / fromIntegral (max 1 (mprTotalWork mpr)))) ++ "x"
  ]
  where roundTo n x = fromIntegral (round (x * 10^(n::Int)) :: Int) / 10^(n::Int)

-- ═══════════════════════════════════════════════════════════
-- KUPERBERG + INTERFERENCE PIPELINE
-- ═══════════════════════════════════════════════════════════

data PipelineIntResult = PIR
  { pirOrigN          :: Int
  , pirOrigSum        :: Int
  , pirReducedWeights :: [Int]
  , pirReducedSum     :: Int
  , pirPrimes         :: [Int]
  , pirReducedCoeffs  :: [Double]
  , pirVerdict        :: Bool
  , pirCorrectAnswer  :: Bool
  , pirCorrect        :: Bool
  , pirTotalWork      :: Int
  , pirDPWork         :: Int
  } deriving (Show)

kuperbergThenInterference :: [Int] -> Int -> [Int] -> PipelineIntResult
kuperbergThenInterference weights target primes =
  let n = length weights
      origBits = ceiling (logBase 2 (fromIntegral (maximum weights) + 1) :: Double)
      bitsToMatch = max 1 (floor (sqrt (fromIntegral origBits) :: Double))
      mask = (2 ^ bitsToMatch) - 1
      -- Group by low bits and pair
      grouped = groupByLowBits mask weights
      (diffs, unpaired) = pairAndDiff' grouped bitsToMatch
      reduced = filter (> 0) (diffs ++ unpaired)
      -- Interference on reduced
      reducedTarget = target `div` (2 ^ bitsToMatch)
      mpr = multiPrimeTest reduced reducedTarget primes
      dpAnswer = Set.member target (dpReachable weights)
      dpWork = Set.size (dpReachable weights)
      totalWork = n + length reduced * sum primes
  in PIR n (sum weights) reduced (sum reduced) primes
         (mprCoeffs mpr) (mprVerdict mpr) dpAnswer
         (mprVerdict mpr == dpAnswer) totalWork dpWork

groupByLowBits :: Int -> [Int] -> [[Int]]
groupByLowBits mask ws =
  let groups = Map.fromListWith (++) [(w .&. mask, [w]) | w <- ws]
  in Map.elems groups

pairAndDiff' :: [[Int]] -> Int -> ([Int], [Int])
pairAndDiff' groups shift = go groups [] []
  where
    go [] diffs unpaired = (diffs, unpaired)
    go (g:gs) diffs unpaired =
      let (d, u) = processPairs g shift
      in go gs (diffs ++ d) (unpaired ++ u)
    processPairs [] _ = ([], [])
    processPairs [x] s = ([], [x `div` (2^s)])
    processPairs (a:b:rest) s =
      let (d, u) = processPairs rest s
      in (abs (a-b) `div` (2^s) : d, u)

showPipelineIntResult :: PipelineIntResult -> String
showPipelineIntResult pir = unlines
  [ "  Orig: n=" ++ show (pirOrigN pir) ++ " sum=" ++ show (pirOrigSum pir)
  , "  Reduced: " ++ show (pirReducedWeights pir) ++ " sum=" ++ show (pirReducedSum pir)
  , "  Coeffs: " ++ show (map (\c -> fromIntegral (round (c*10)::Int)/10) (pirReducedCoeffs pir))
  , "  Verdict: " ++ (if pirVerdict pir then "YES" else "NO")
      ++ " correct=" ++ show (pirCorrectAnswer pir)
      ++ " " ++ (if pirCorrect pir then "✓" else "✗")
  , "  Work: " ++ show (pirTotalWork pir) ++ " vs DP: " ++ show (pirDPWork pir)
  ]
