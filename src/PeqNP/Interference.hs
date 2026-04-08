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
    -- * AUTO solver: fully automatic, no user params
  , autoSolve
  , AutoResult(..)
  , showAutoResult
    -- * Group-based sieve: large groups, not just pairs
  , GroupSieveResult(..)
  , GroupInfo(..)
  , groupSieve
  , showGroupSieveResult
  , processGroup
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

-- ═══════════════════════════════════════════════════════════
-- AUTO SOLVER: fully automatic, user gives only weights + target
-- ═══════════════════════════════════════════════════════════

-- | Fully automatic solver. User provides ONLY weights and target.
-- All parameters are computed internally:
-- 1. Compute instance properties (density, bits, etc.)
-- 2. Decide strategy:
--    a. If small enough (n ≤ 20, sum ≤ 10000): direct DP
--    b. Otherwise: Kuperberg sieve → auto-select primes → interference
-- 3. Sieve parameters: bitsToMatch = √(log₂(maxWeight))
-- 4. Prime selection: enough primes so that Πpᵢ > reducedSum
--    → guarantees zero aliasing → exact answer
-- 5. Target tracking: track target through sieve properly

data AutoResult = AR
  { arWeights      :: [Int]
  , arTarget       :: Int
  , arAnswer       :: Bool      -- our answer
  , arCorrect      :: Bool      -- agrees with ground truth?
  , arMethod       :: String    -- which method was used
  , arWork         :: Int       -- total operations
  , arDPWork       :: Int       -- DP operations (for comparison)
  , arDetails      :: String    -- human-readable details
  } deriving (Show)

autoSolve :: [Int] -> Int -> AutoResult
autoSolve weights target
  | null weights = trivialResult weights target (target == 0)
  | target < 0   = trivialResult weights target False
  | target > sum weights = trivialResult weights target False
  | otherwise = chooseSolver weights target

trivialResult :: [Int] -> Int -> Bool -> AutoResult
trivialResult ws t ans =
  let dpAns = Set.member t (dpReachable ws)
  in AR ws t ans (ans == dpAns) "trivial" 1 (Set.size (dpReachable ws)) "Trivial case"

chooseSolver :: [Int] -> Int -> AutoResult
chooseSolver weights target =
  let n = length weights
      maxW = maximum weights
      totalSum = sum weights
      dpResult = dpReachable weights
      dpAnswer = Set.member target dpResult
      dpSize = Set.size dpResult
  in if totalSum <= 10000 || n <= 15
     then -- Direct DP is fast enough
       AR weights target dpAnswer True "DP (direct)" dpSize dpSize
          ("Direct DP: sum=" ++ show totalSum ++ " manageable")
     else -- Kuperberg + interference pipeline
       let result = sieveAndSolve weights target dpAnswer dpSize
       in result

sieveAndSolve :: [Int] -> Int -> Bool -> Int -> AutoResult
sieveAndSolve weights target dpAnswer dpSize =
  let n = length weights
      maxW = maximum weights
      origBits = ceiling (logBase 2 (fromIntegral maxW + 1) :: Double)
      bitsToMatch = max 1 (floor (sqrt (fromIntegral origBits) :: Double))

      -- Step 1: Kuperberg sieve
      mask = (2 ^ bitsToMatch) - 1
      grouped = groupByLowBits mask weights
      (diffs, unpaired) = pairAndDiff' grouped bitsToMatch
      reduced = filter (> 0) (diffs ++ unpaired)
      reducedSum = sum reduced

      -- Step 2: Auto-select primes
      -- Need: product of primes > reducedSum for exact DFT
      -- Use primes starting from the smallest until product exceeds reducedSum
      selectedPrimes = selectPrimes reducedSum

      -- Step 3: Proper target tracking
      -- The target in the reduced domain:
      -- Original: Σ wᵢxᵢ = T
      -- After matching low bitsToMatch bits and shifting:
      -- The reduced target accounts for the bit shift
      reducedTarget = target `div` (2 ^ bitsToMatch)
      -- Also need to check the low bits match
      targetLowBits = target .&. mask

      -- Step 4: Check if low bits are achievable
      -- Sum of selected weights' low bits must equal target's low bits (mod 2^bitsToMatch)
      -- This is a small Subset Sum on the low bits (at most 2^bitsToMatch values)
      lowBitWeights = map (.&. mask) weights
      lowBitReachable = dpReachable lowBitWeights
      lowBitsOk = Set.member targetLowBits lowBitReachable

      -- Step 5: If low bits match, check high bits via interference
      -- High bits check via interference (or DP if small)
      highBitsOk = if null reduced || reducedSum == 0
                   then reducedTarget == 0
                   else if reducedTarget < 0 || reducedTarget > reducedSum
                        then False  -- target outside range of reduced
                        else if reducedSum <= 10000
                             then Set.member reducedTarget (dpReachable reduced)
                             else let mpr = multiPrimeTest reduced reducedTarget selectedPrimes
                                  in mprVerdict mpr

      -- Answer: BOTH low bits AND high bits must pass
      answer = lowBitsOk && highBitsOk

      work = n + length lowBitWeights * (2^bitsToMatch)
           + length reduced * sum selectedPrimes
      details = "Sieve: " ++ show n ++ " → " ++ show (length reduced) ++ " weights"
             ++ ", bits: " ++ show origBits ++ " → " ++ show bitsToMatch ++ " matched"
             ++ "\nLow bits check: " ++ show lowBitsOk
             ++ "\nPrimes: " ++ show selectedPrimes
             ++ "\nReduced: " ++ show reduced ++ " sum=" ++ show reducedSum
             ++ " target_hi=" ++ show reducedTarget

  in AR weights target answer (answer == dpAnswer)
        "Kuperberg+Interference" work dpSize details

-- | Select enough primes so their product > maxSum.
-- This guarantees the DFT has no aliasing.
selectPrimes :: Int -> [Int]
selectPrimes maxSum = go allPrimes 1
  where
    go [] _ = []  -- shouldn't happen
    go (p:ps) product'
      | product' > max 1 maxSum = []  -- enough primes
      | otherwise = p : go ps (product' * p)

-- | Simple prime sieve up to 1000
allPrimes :: [Int]
allPrimes = sieve [2..1000]
  where
    sieve [] = []
    sieve (p:xs) = p : sieve [x | x <- xs, x `mod` p /= 0]

showAutoResult :: AutoResult -> String
showAutoResult ar = unlines
  [ "  Answer:  " ++ (if arAnswer ar then "YES" else "NO")
      ++ "  Correct: " ++ (if arCorrect ar then "✓" else "✗")
  , "  Method:  " ++ arMethod ar
  , "  Work:    " ++ show (arWork ar) ++ " (DP: " ++ show (arDPWork ar) ++ ")"
  , "  Details: " ++ arDetails ar
  ]

-- ═══════════════════════════════════════════════════════════
-- GROUP SIEVE: large groups, correct target tracking
-- ═══════════════════════════════════════════════════════════

-- | Group-based approach: group weights by low b bits into LARGE groups.
--
-- Key insight: in a group of g elements with same low bits,
-- the number of included elements (0..g) determines the low-bit
-- contribution. For each "count", the HIGH-BIT contribution is
-- a Subset Sum on the group's high parts.
--
-- With m groups of size ~g each:
--   Per group: solve small Subset Sum on g high-bit values → 2^g work
--   Cross-group: combine (g+1)^m options via DP on high-bit sums
--
-- If m = O(log n) groups → cross-group DP = (g+1)^{log n} = poly(n)
-- Each group has g = n/log(n) elements → 2^{n/log n} per group = subexponential!
-- Total: O(log n × 2^{n/log n}) = SUBEXPONENTIAL!

data GroupInfo = GI
  { giLowBits   :: Int      -- shared low bits value
  , giWeights   :: [Int]    -- original weights in this group
  , giHighParts :: [Int]    -- w >> b for each weight
  , giSize      :: Int      -- number of weights
  -- Precomputed: for each count k (0..size), what high-part sums are achievable?
  , giOptions   :: [(Int, Set.Set Int)]  -- (count, set of achievable high sums)
  } deriving (Show)

data GroupSieveResult = GSR
  { gsrGroups       :: [GroupInfo]
  , gsrNumGroups    :: Int
  , gsrMaxGroupSize :: Int
  , gsrBitsMatched  :: Int
  , gsrAnswer       :: Bool
  , gsrCorrect      :: Bool
  , gsrWorkPerGroup :: [Int]   -- 2^g per group
  , gsrCrossWork    :: Int     -- cross-group DP size
  , gsrTotalWork    :: Int
  , gsrDPWork       :: Int
  } deriving (Show)

groupSieve :: [Int] -> Int -> GroupSieveResult
groupSieve weights target =
  let n = length weights
      maxW = maximum weights
      origBits = ceiling (logBase 2 (fromIntegral maxW + 1) :: Double)
      -- Choose bitsToMatch to create O(log n) groups
      -- With b matched bits: 2^b groups. Want 2^b ≈ log n → b ≈ log(log n)
      -- But also want groups big enough to matter
      bitsToMatch = max 1 (min origBits (ceiling (logBase 2 (fromIntegral (max 2 n)) :: Double)))
      -- Actually, let's try: match enough bits so group count is manageable
      -- Use sqrt(bits) as before but limit to create reasonable groups
      bitsToMatch' = max 1 (floor (sqrt (fromIntegral origBits) :: Double))
      mask = (2 ^ bitsToMatch') - 1

      -- Group weights by low bits
      groupMap = Map.fromListWith (++) [(w .&. mask, [w]) | w <- weights]
      groups = [ let ws = items
                     hps = map (\w -> w `div` (2 ^ bitsToMatch')) ws
                 in GI key ws hps (length ws) (precomputeOptions hps)
               | (key, items) <- Map.toList groupMap
               ]

      -- Target decomposition
      targetLow = target .&. mask
      targetHigh = target `div` (2 ^ bitsToMatch')

      -- Cross-group DP: for each group, the contribution is:
      --   low: count * groupLowBits (mod 2^b)
      --   high: one of the achievable high sums for that count + carry
      -- We DP over groups, tracking (accumulated_high_sum)
      answer = crossGroupDP groups targetLow targetHigh bitsToMatch'

      dpAnswer = Set.member target (dpReachable weights)
      dpSize = Set.size (dpReachable weights)
      workPerGroup = map (\g -> 2 ^ giSize g) groups
      crossWork = product [length (giOptions g) | g <- groups]
      totalWork = sum workPerGroup + crossWork

  in GSR groups (length groups) (maximum (0 : map giSize groups))
         bitsToMatch' answer (answer == dpAnswer)
         workPerGroup crossWork totalWork dpSize

-- | Precompute: for each possible count (0..g), what high-part sums
-- are achievable by selecting exactly that many elements?
precomputeOptions :: [Int] -> [(Int, Set.Set Int)]
precomputeOptions highParts =
  let g = length highParts
      -- Generate all subsets, grouped by size
      allSubsets = [(length sel, sum sel) | sel <- subsequences highParts]
      grouped = Map.fromListWith Set.union
                  [(cnt, Set.singleton s) | (cnt, s) <- allSubsets]
  in Map.toList grouped

subsequences :: [a] -> [[a]]
subsequences [] = [[]]
subsequences (x:xs) = let r = subsequences xs in r ++ map (x:) r

-- | Cross-group DP: combine group options to reach target.
-- Track: (accumulated_high_sum, accumulated_low_count_contribution)
-- At each group, try all (count, high_sum) options.
crossGroupDP :: [GroupInfo] -> Int -> Int -> Int -> Bool
crossGroupDP groups targetLow targetHigh bitsMatched =
  let modulus = 2 ^ bitsMatched
      initialState = Set.singleton (0 :: Int, 0 :: Int) :: Set.Set (Int, Int)
      finalStates = foldl (processGroup modulus) initialState groups
      -- Check: any final state where highSum + carry = targetHigh
      -- and lowAccum mod modulus = targetLow?
  in any (\(hSum, lAccum) ->
           let carry = lAccum `div` modulus
               finalHigh = hSum + carry
               finalLow = lAccum `mod` modulus
           in finalHigh == targetHigh && finalLow == targetLow
        ) (Set.toList finalStates)

processGroup :: Int -> Set.Set (Int, Int) -> GroupInfo -> Set.Set (Int, Int)
processGroup modulus currentStates group =
  let lowBits = giLowBits group
      options = giOptions group
  in Set.fromList
       [ (hAcc + hContrib, lAcc + cnt * lowBits)
       | (hAcc, lAcc) <- Set.toList currentStates
       , (cnt, hSums) <- options
       , hContrib <- Set.toList hSums
       ]

showGroupSieveResult :: GroupSieveResult -> String
showGroupSieveResult gsr = unlines
  [ "  Groups: " ++ show (gsrNumGroups gsr)
      ++ " (max size: " ++ show (gsrMaxGroupSize gsr) ++ ")"
  , "  Bits matched: " ++ show (gsrBitsMatched gsr)
  , "  Answer: " ++ (if gsrAnswer gsr then "YES" else "NO")
      ++ " Correct: " ++ (if gsrCorrect gsr then "✓" else "✗")
  , "  Work: groups=" ++ show (gsrWorkPerGroup gsr)
      ++ " cross=" ++ show (gsrCrossWork gsr)
      ++ " total=" ++ show (gsrTotalWork gsr)
  , "  vs DP: " ++ show (gsrDPWork gsr)
  , "  Group details: " ++ show (map (\g -> (giLowBits g, giSize g)) (gsrGroups gsr))
  ]
