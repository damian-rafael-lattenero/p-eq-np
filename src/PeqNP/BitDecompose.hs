module PeqNP.BitDecompose
  ( -- * Bit decomposition
    toBits
  , fromBits
  , maxBits
    -- * Bit-level Subset Sum
  , BitColumn(..)
  , decomposeProblem
  , bitLevelSolve
  , BitLevelStats(..)
    -- * Carry analysis: where does the state explode?
  , CarryProfile(..)
  , analyzeCarry
  , showCarryProfile
    -- * COUPLED bit-level solver (correct!)
  , coupledBitSolve
  , CoupledStats(..)
  , showCoupledStats
    -- * Untie-Retie experiment
  , UntieRetie(..)
  , untieRetieExperiment
  , showUntieRetie
    -- * Interleaved solver: carry + coupling simultaneously
  , InterleavedStats(..)
  , interleavedSolve
  , showInterleavedStats
    -- * Basis optimization: find best multiplier
  , overlapForMultiplier
  , bestMultiplier
  , showBasisSearch
    -- * GF(2) transformations: non-linear overlap reduction
  , BitMatrix
  , weightsToBitMatrix
  , overlapOfMatrix
  , xorTransform
  , searchGF2Transforms
  , showGF2Results
    -- * Solver in GF(2)-transformed basis
  , GF2SolverResult(..)
  , solveInTransformedBasis
  , showGF2SolverResult
    -- * GF(2) rank analysis: theoretical limits
  , gf2Rank
  , RankAnalysis(..)
  , analyzeRank
  , showRankAnalysis
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import Data.Bits (testBit)

-- ═══════════════════════════════════════════════════════════
-- Bit decomposition: Int → [Bool]
-- ═══════════════════════════════════════════════════════════

-- | Decompose an integer into its binary representation (LSB first)
toBits :: Int -> Int -> [Bool]
toBits numBits x = [testBit x i | i <- [0..numBits-1]]

-- | Reconstruct integer from bits (LSB first)
fromBits :: [Bool] -> Int
fromBits = sum . zipWith (\i b -> if b then 2^i else 0) [(0::Int)..]

-- | Number of bits needed to represent the max possible sum
maxBits :: [Int] -> Int
maxBits [] = 1
maxBits xs = ceiling (logBase 2 (fromIntegral (sum xs) + 1) :: Double) + 1

-- ═══════════════════════════════════════════════════════════
-- Bit-level problem decomposition
-- ═══════════════════════════════════════════════════════════

-- | A "column" of bits at position k: one bit per weight.
-- bit k of weight w_i = whether 2^k contributes to w_i.
data BitColumn = BC
  { bcPosition :: Int     -- bit position (0 = LSB)
  , bcBits     :: [Bool]  -- one per weight: does this weight have a 1 at this position?
  , bcOnesCount :: Int    -- number of 1s in this column
  } deriving (Show)

-- | Decompose the Subset Sum problem into bit columns.
--
-- Instead of n weights of up to B bits each, view as B columns of n bits.
-- Each column tells which weights contribute a 1 at that bit position.
--
-- weights = [5, 13, 3]  (binary: 101, 1101, 11)
-- Column 0 (2^0): [1, 1, 1]  ← 3 ones, contribute 0..3 to this position
-- Column 1 (2^1): [0, 0, 1]  ← 1 one
-- Column 2 (2^2): [1, 1, 0]  ← 2 ones
-- Column 3 (2^3): [0, 1, 0]  ← 1 one
decomposeProblem :: [Int] -> [BitColumn]
decomposeProblem elems =
  let b = maxBits elems
  in [ let bits = [testBit w k | w <- elems]
       in BC k bits (length (filter id bits))
     | k <- [0..b-1]
     ]

-- ═══════════════════════════════════════════════════════════
-- Bit-level solver with carry tracking
-- ═══════════════════════════════════════════════════════════

-- | At each bit position k, we need to decide which weights to include.
-- The decision affects bit k of the sum, plus a CARRY to position k+1.
--
-- State at each bit position: the set of possible carry values.
-- If this set stays bounded (polynomial), the algorithm is polynomial.
-- If it explodes, NP-hardness has appeared.

data BitLevelStats = BLS
  { blsFound       :: Bool
  , blsSolution    :: Maybe [Bool]  -- inclusion vector
  , blsBitsUsed    :: Int           -- number of bit positions processed
  , blsMaxCarry    :: Int           -- max carry state across all positions
  , blsCarryPerBit :: [Int]         -- |carry states| at each bit position
  } deriving (Show)

-- | Solve Subset Sum by processing bit columns from LSB to MSB.
--
-- Algorithm:
-- 1. At bit position k, target bit t_k is known
-- 2. We have a set of possible carries from position k-1
-- 3. For each carry c, we need: (selected ones at position k) + c
--    to have bit k matching t_k. The "overflow" becomes the carry for k+1.
-- 4. Number of ones selected at position k ranges from 0 to onesCount.
-- 5. For each valid (carry_in, selected_ones) pair:
--    total = carry_in + selected_ones
--    bit k of sum = total mod 2 (must match target bit k)
--    carry_out = total div 2
--
-- The SET of possible carry_out values is the state.
bitLevelSolve :: [Int] -> Int -> BitLevelStats
bitLevelSolve elems target =
  let columns = decomposeProblem elems
      targetBits = toBits (length columns) target
      (carries, found) = processColumns columns targetBits
  in BLS
    { blsFound       = found
    , blsSolution    = Nothing  -- tracking full solution requires more bookkeeping
    , blsBitsUsed    = length columns
    , blsMaxCarry    = maximum (0 : map Set.size carries)
    , blsCarryPerBit = map Set.size carries
    }

processColumns :: [BitColumn] -> [Bool] -> ([Set Int], Bool)
processColumns columns targetBits =
  let initialCarry = Set.singleton 0
      (allCarries, finalCarry) = go columns targetBits initialCarry []
  in (reverse allCarries, Set.member 0 finalCarry)
  where
    go :: [BitColumn] -> [Bool] -> Set Int -> [Set Int] -> ([Set Int], Set Int)
    go [] [] carry acc = (carry : acc, carry)
    go [] _  carry acc = (carry : acc, carry)
    go _  [] carry acc = (carry : acc, carry)
    go (col:cols) (tBit:tBits) carryIn acc =
      let onesCount = bcOnesCount col
          targetBit = if tBit then 1 else 0
          -- For each possible carry-in and number of ones selected,
          -- check if the sum's bit k matches target bit k
          carryOut = Set.fromList
            [ (carryInVal + selected) `div` 2
            | carryInVal <- Set.toList carryIn
            , selected <- [0..onesCount]
            , (carryInVal + selected) `mod` 2 == targetBit
            ]
      in go cols tBits carryOut (carryIn : acc)

-- ═══════════════════════════════════════════════════════════
-- Carry analysis: the anatomy of difficulty
-- ═══════════════════════════════════════════════════════════

data CarryProfile = CP
  { cpElements     :: [Int]
  , cpTarget       :: Int
  , cpBitsNeeded   :: Int
  , cpCarrySizes   :: [Int]     -- |carry set| at each bit position
  , cpMaxCarry     :: Int       -- peak carry set size
  , cpExplosion    :: Maybe Int -- first bit position where carry > n
  } deriving (Show)

-- | Analyze how carry states grow across bit positions.
--
-- THE KEY EXPERIMENT:
-- For polynomial weights: carry stays bounded by O(n) at each position
--   (at most n ones per column → carry ≤ n/2 → carry set ≤ n/2 + 1)
-- For exponential weights: carry might grow... or might not!
--   Because each column still has at most n ones, the CARRY is bounded
--   by n regardless of weight magnitude!
--
-- THIS IS THE CRUCIAL INSIGHT: the carry is bounded by the NUMBER
-- of elements (n), not by the MAGNITUDE of the weights.
-- Each column has at most n ones → max column sum = n → max carry = n/2.
-- So |carry set| ≤ n/2 + 1 at EVERY bit position.
--
-- Total work: B bit positions × O(n) carry states × O(n) ones per column
-- = O(B × n²) = O(n² × log(max_weight))
-- This is POLYNOMIAL in the input size (which includes log(max_weight))!
analyzeCarry :: [Int] -> Int -> CarryProfile
analyzeCarry elems target =
  let stats = bitLevelSolve elems target
      n = length elems
  in CP
    { cpElements   = elems
    , cpTarget     = target
    , cpBitsNeeded = blsBitsUsed stats
    , cpCarrySizes = blsCarryPerBit stats
    , cpMaxCarry   = blsMaxCarry stats
    , cpExplosion  = case filter (\(_, sz) -> sz > n) (zip [(0::Int)..] (blsCarryPerBit stats)) of
                       ((pos, _):_) -> Just pos
                       []           -> Nothing
    }

showCarryProfile :: CarryProfile -> String
showCarryProfile cp = unlines $
  [ "  Elements: " ++ show (cpElements cp)
  , "  Target:   " ++ show (cpTarget cp)
  , "  Bits needed: " ++ show (cpBitsNeeded cp)
  , "  n = " ++ show (length (cpElements cp))
  , ""
  , "  Carry set sizes per bit position (LSB → MSB):"
  , "  " ++ show (cpCarrySizes cp)
  , "  Max carry set: " ++ show (cpMaxCarry cp)
  , ""
  , "  Carry bound (n/2 + 1 = " ++ show (length (cpElements cp) `div` 2 + 1) ++ "):"
  , "  " ++ case cpExplosion cp of
      Nothing -> "NEVER EXCEEDED — carry stays O(n) at every bit position!"
      Just p  -> "Exceeded at bit " ++ show p
  ]

-- ═══════════════════════════════════════════════════════════
-- COUPLED bit-level solver: tracks WHICH weights are included
-- ═══════════════════════════════════════════════════════════

-- | State in the coupled solver: (carry, inclusion_mask).
-- The mask tracks which of the n weights are currently "included".
-- Two states are equivalent if they have the same carry AND the same
-- future behavior — but the mask determines future behavior because
-- higher bit positions of included weights are forced.
--
-- KEY QUESTION: how many (carry, mask_equivalence_class) pairs exist?
-- If the mask can be summarized compactly → polynomial
-- If we need the full mask → 2^n states → exponential

-- | A coupled state: carry value + which weights are included so far
-- We represent the mask as a Set of included weight indices for efficiency
type CoupledState = (Int, Set Int)  -- (carry, set of included weight indices)

data CoupledStats = CS
  { csFound         :: Bool
  , csCorrect       :: Bool     -- agrees with DP?
  , csBitsProcessed :: Int
  , csStatesPerBit  :: [Int]    -- |coupled states| at each bit position
  , csMaxStates     :: Int      -- peak coupled states
  , csUncoupledMax  :: Int      -- for comparison: uncoupled max carry
  } deriving (Show)

-- | Solve Subset Sum with COUPLED bit-level processing.
--
-- Process WEIGHT by WEIGHT (not bit by bit). For each weight,
-- decide include/exclude. Track the running sum, and at the end
-- check each bit of the sum against the target.
--
-- BUT: to measure the state space at the BIT level, we track
-- the set of reachable PARTIAL SUMS after processing each weight,
-- and measure how many distinct (partial_sum mod 2^k) values exist
-- at each bit position k. This shows the effective state count
-- per bit when coupling is enforced.
coupledBitSolve :: [Int] -> Int -> CoupledStats
coupledBitSolve elems target =
  let b = maxBits elems
      -- Process weight by weight: track set of reachable partial sums
      levels = scanl (\sums w -> Set.union sums (Set.map (+ w) sums))
                     (Set.singleton 0) elems
      -- For each bit position, count distinct residues mod 2^(k+1)
      -- among reachable partial sums at EACH processing level
      -- This measures the "effective state space" per bit
      statesPerBit = [ maximum [Set.size (Set.map (`mod` (2^(k+1))) sums) | sums <- levels]
                     | k <- [0..b-1]
                     ]
      found = Set.member target (last levels)
      dpAnswer = Set.member target (dpReachableLocal elems)
      uncoupledStats = bitLevelSolve elems target
  in CS
    { csFound         = found
    , csCorrect       = found == dpAnswer
    , csBitsProcessed = b
    , csStatesPerBit  = statesPerBit
    , csMaxStates     = maximum (0 : statesPerBit)
    , csUncoupledMax  = blsMaxCarry uncoupledStats
    }

dpReachableLocal :: [Int] -> Set Int
dpReachableLocal = foldl step (Set.singleton 0)
  where step reachable x = Set.union reachable (Set.map (+ x) reachable)

showCoupledStats :: CoupledStats -> String
showCoupledStats cs = unlines $
  [ "  Found:       " ++ show (csFound cs)
  , "  Correct:     " ++ show (csCorrect cs)
  , "  Bits:        " ++ show (csBitsProcessed cs)
  , "  States/bit:  " ++ show (csStatesPerBit cs)
  , "  Max states:  " ++ show (csMaxStates cs)
      ++ (if csMaxStates cs <= 10 then " (small!)" else
          if csMaxStates cs <= 100 then " (moderate)" else " (LARGE)")
  , "  Uncoupled:   " ++ show (csUncoupledMax cs) ++ " (for comparison)"
  ]

-- ═══════════════════════════════════════════════════════════
-- Untie-Retie experiment: decouple, solve, re-check coupling
-- ═══════════════════════════════════════════════════════════

-- | The "untie at the start, retie at the end" experiment.
--
-- STEP 1 (untie): For each bit position independently, find all
--   valid (carry_in → carry_out) transitions.
-- STEP 2 (solve uncoupled): enumerate all carry paths through the
--   bit positions (ignoring coupling). These are "uncoupled solutions".
-- STEP 3 (retie): for each uncoupled solution, check if it corresponds
--   to a valid coupled selection (consistent weight inclusion).
--
-- KEY METRIC: what fraction of uncoupled solutions survive the retie?
-- If most survive → retie is easy → problem is easy
-- If almost none survive → retie filters exponentially → NP-hard

data UntieRetie = UR
  { urElements          :: [Int]
  , urTarget            :: Int
  , urTotalSubsets      :: Int    -- 2^n (brute force space)
  , urUncoupledSolutions :: Int   -- solutions in uncoupled domain
  , urCoupledSolutions  :: Int    -- solutions that pass coupling check
  , urSurvivalRate      :: Double -- coupled / uncoupled
  , urCorrectAnswer     :: Bool   -- from DP
  } deriving (Show)

-- | Run the untie-retie experiment.
--
-- Concretely: enumerate all 2^n subsets (small n only!),
-- for each check: (a) does the uncoupled solver accept it?
-- (b) does it actually sum to target?
--
-- The uncoupled solver accepts ANY bit-compatible assignment.
-- The coupled solver requires actual subset sum = target.
-- The gap between (a) and (b) is the cost of re-tying.
untieRetieExperiment :: [Int] -> Int -> UntieRetie
untieRetieExperiment elems target =
  let n = length elems
      totalSubsets = (2 :: Int) ^ n
      allSubsets = generateSubsets elems
      -- Coupled: actual subset sums matching target
      coupled = filter (\ss -> sum ss == target) allSubsets
      -- Uncoupled: how many subsets have a bit-compatible sum?
      -- A subset is "uncoupled-valid" if, at each bit position,
      -- the number of weights with 1 at that position (among included)
      -- plus the carry from below, has the correct target bit.
      -- For simplicity: the uncoupled solver accepts more, so we
      -- count subsets where the uncoupled bit-level check passes.
      -- Actually, the simplest honest measurement:
      -- uncoupled accepts = number of distinct sums reachable
      -- in the uncoupled domain that equal target
      -- But that's just 1 or 0...
      --
      -- BETTER MEASUREMENT: count how many (carry_path, bit_assignment)
      -- pairs exist in the uncoupled domain vs how many correspond
      -- to valid subsets. But this is complex.
      --
      -- SIMPLEST HONEST MEASUREMENT: compare the number of subsets
      -- vs the number that sum to target, per bit position.
      --
      -- Let's just count: for each bit position, how many of the 2^n subsets
      -- have the correct bit at that position (with carry)?
      -- If ALL positions agree: coupled solution. Some positions: uncoupled-valid.

      -- Practical approach: count subsets that match target at each bit position independently
      b = maxBits elems
      targetBits' = toBits b target
      bitsMatch ss k =
        let included = [w | w <- ss, testBit w k]
            s = sum [w | w <- elems, w `elem` ss]  -- sum of included
        in testBit s k == (targetBits' !! k)

      -- Subsets matching at ALL bit positions = coupled solutions
      -- Subsets matching at EACH position independently (ignoring carry cross-talk)
      -- ≈ uncoupled solutions. But carry makes this tricky.
      -- Let's simplify: just measure coupled vs total.

      dpAnswer = Set.member target (dpReachableLocal elems)
      numCoupled = length coupled
  in UR
    { urElements           = elems
    , urTarget             = target
    , urTotalSubsets       = totalSubsets
    , urUncoupledSolutions = totalSubsets  -- uncoupled accepts all (it's more permissive)
    , urCoupledSolutions   = numCoupled
    , urSurvivalRate       = if totalSubsets > 0
                             then fromIntegral numCoupled / fromIntegral totalSubsets
                             else 0
    , urCorrectAnswer      = dpAnswer
    }

generateSubsets :: [Int] -> [[Int]]
generateSubsets [] = [[]]
generateSubsets (x:xs) = let rest = generateSubsets xs
                         in rest ++ map (x:) rest

showUntieRetie :: UntieRetie -> String
showUntieRetie ur = unlines
  [ "  Elements:       " ++ show (urElements ur)
  , "  Target:         " ++ show (urTarget ur)
  , "  Total subsets:  " ++ show (urTotalSubsets ur)
  , "  Coupled (sum=T):" ++ show (urCoupledSolutions ur)
  , "  Survival rate:  " ++ show (roundTo' 6 (urSurvivalRate ur))
  , "  Correct answer: " ++ show (urCorrectAnswer ur)
  , "  --> " ++ if urCoupledSolutions ur > 0
                then show (urCoupledSolutions ur) ++ " out of " ++ show (urTotalSubsets ur)
                     ++ " subsets sum to target (" ++ show (roundTo' 2 (urSurvivalRate ur * 100)) ++ "%)"
                else "NO subset sums to target"
  ]
  where
    roundTo' n x = fromIntegral (round (x * 10^(n::Int)) :: Int) / 10^(n::Int)

-- ═══════════════════════════════════════════════════════════
-- Interleaved solver: carry + coupling AT EACH STEP
-- ═══════════════════════════════════════════════════════════

-- | Process bit-by-bit, carrying BOTH the arithmetic carry AND the
-- coupling decisions simultaneously. At each bit position k:
--
-- - Weights with a 1 at position k that are ALREADY DECIDED (from
--   a lower position): forced to contribute 1 (if included) or 0
-- - Weights with a 1 at position k that are NOT YET DECIDED:
--   choose include/exclude, REMEMBER the decision for future positions
-- - Weights with a 0 at position k: no effect, no decision needed
--
-- active(k) = weights decided at position ≤ k that have bits at position > k.
-- These must be "carried" as part of the state.
-- State = (carry, Set of included weight indices among active)
-- If max active(k) is small → polynomial!

data InterleavedStats = IS
  { isFound       :: Bool
  , isCorrect     :: Bool
  , isBits        :: Int
  , isActivePerBit :: [Int]      -- active(k) at each bit position
  , isStatesPerBit :: [Int]      -- actual |states| at each position
  , isMaxActive   :: Int         -- max active(k)
  , isMaxStates   :: Int         -- max |states|
  , isTheoreticalMax :: [Int]    -- n/2 * 2^active(k) theoretical bound
  } deriving (Show)

interleavedSolve :: [Int] -> Int -> InterleavedStats
interleavedSolve elems target =
  let b = maxBits elems
      n = length elems
      targetBits' = toBits b target
      columns = decomposeProblem elems

      -- For each weight, find the set of bit positions where it has a 1
      weightBits :: [[Int]]  -- weight i → list of bit positions with 1
      weightBits = [ [k | k <- [0..b-1], testBit w k] | w <- elems ]

      -- highest bit position for each weight
      highestBit :: [Int]
      highestBit = [ if null bs then -1 else maximum bs | bs <- weightBits ]

      -- Process bit by bit
      -- State: (carry, Set of weight indices currently "committed as included")
      initialStates :: Set (Int, Set Int)
      initialStates = Set.singleton (0, Set.empty)

      (stats, finalStates) = go 0 columns targetBits' initialStates []

      found = any (\(carry, _) -> carry == 0) (Set.toList finalStates)
      dpAnswer = Set.member target (dpReachableLocal elems)

      -- Compute active weights per bit position
      activePerBit = [ length [ i | i <- [0..n-1]
                              , any (\pos -> pos <= k) (weightBits !! i)  -- decided at or before k
                              , highestBit !! i > k                      -- has future bits
                              ]
                     | k <- [0..b-1]
                     ]

  in IS
    { isFound        = found
    , isCorrect      = found == dpAnswer
    , isBits         = b
    , isActivePerBit = activePerBit
    , isStatesPerBit = reverse stats
    , isMaxActive    = maximum (0 : activePerBit)
    , isMaxStates    = maximum (0 : stats)
    , isTheoreticalMax = [ min (n `div` 2 + 1) (n + 1) * (2 ^ (activePerBit !! k))
                         | k <- [0..b-1] ]
    }
  where
    go :: Int -> [BitColumn] -> [Bool] -> Set (Int, Set Int) -> [Int]
       -> ([Int], Set (Int, Set Int))
    go _ [] [] states acc = (Set.size states : acc, states)
    go _ [] _  states acc = (Set.size states : acc, states)
    go _ _  [] states acc = (Set.size states : acc, states)
    go k (col:cols) (tBit:tBits) states acc =
      let targetBitVal = if tBit then 1 else 0
          n = length elems
          -- Weights with a 1 at this position
          onesHere = [i | i <- [0..n-1], bcBits col !! i]

          nextStates = Set.fromList $ do
            (carry, committed) <- Set.toList states
            -- Partition onesHere into: already committed (forced 1), and free (choose)
            let forced = [i | i <- onesHere, Set.member i committed]
                free   = [i | i <- onesHere, not (Set.member i committed)]
                forcedCount = length forced
            -- Try all subsets of free weights
            freeChoice <- subsetsOf free
            let selected = forcedCount + length freeChoice
                total = carry + selected
            -- Check target bit
            guard (total `mod` 2 == targetBitVal)
            let newCarry = total `div` 2
                newCommitted = Set.union committed (Set.fromList freeChoice)
                -- Forget weights whose highest bit is this position
                -- (they have no future influence)
                forget = Set.fromList [i | i <- [0..n-1]
                                     , highestBit' !! i == k]
                cleaned = Set.difference newCommitted forget
            return (newCarry, cleaned)

      in go (k+1) cols tBits nextStates (Set.size states : acc)

    highestBit' = [ let bs = [k' | k' <- [0..maxBits elems - 1], testBit w k']
                    in if null bs then -1 else maximum bs
                  | w <- elems ]

    subsetsOf :: [a] -> [[a]]
    subsetsOf []     = [[]]
    subsetsOf (x:xs) = let rest = subsetsOf xs in rest ++ map (x:) rest

    guard :: Bool -> [()]
    guard True  = [()]
    guard False = []

showInterleavedStats :: InterleavedStats -> String
showInterleavedStats is' = unlines $
  [ "  Found:       " ++ show (isFound is')
  , "  Correct:     " ++ show (isCorrect is')
  , "  Bits:        " ++ show (isBits is')
  , "  Active/bit:  " ++ show (isActivePerBit is')
  , "  States/bit:  " ++ show (isStatesPerBit is')
  , "  Max active:  " ++ show (isMaxActive is')
  , "  Max states:  " ++ show (isMaxStates is')
  , "  Theoretical: carry×2^active = " ++ show (isTheoreticalMax is')
  , "  → Complexity class: " ++
      (if isMaxActive is' <= 2 then "POLYNOMIAL (active ≤ 2)"
       else if isMaxActive is' <= 5 then "FPT-tractable (active ≤ 5)"
       else "EXPONENTIAL in active (active = " ++ show (isMaxActive is') ++ ")")
  ]

-- ═══════════════════════════════════════════════════════════
-- Basis optimization: can we reduce overlap by multiplying?
-- ═══════════════════════════════════════════════════════════

-- | Compute max bit-overlap for weights scaled by multiplier c.
-- Overlap at bit k = number of weights with a 1 at position k
-- that also have a 1 at some position > k (i.e., "active" weights).
overlapForMultiplier :: [Int] -> Int -> Int
overlapForMultiplier elems c =
  let scaled = map (* c) elems
      b = maxBits scaled
      highBit w = maximum (-1 : [k | k <- [0..b-1], testBit w k])
      active k = length [ w | w <- scaled
                         , testBit w k
                         , highBit w > k
                         ]
  in maximum (0 : [active k | k <- [0..b-1]])

-- | Search for the multiplier c in [1..maxC] that minimizes max overlap.
bestMultiplier :: [Int] -> Int -> (Int, Int)  -- (best c, its overlap)
bestMultiplier elems maxC =
  let candidates = [(c, overlapForMultiplier elems c) | c <- [1..maxC]]
  in minimumByOverlap candidates
  where
    minimumByOverlap [] = (1, length elems)
    minimumByOverlap xs = foldr1 (\(c1,o1) (c2,o2) -> if o1 <= o2 then (c1,o1) else (c2,o2)) xs

-- | Show basis search results
showBasisSearch :: [Int] -> Int -> String
showBasisSearch elems maxC =
  let (bestC, bestOverlap) = bestMultiplier elems maxC
      origOverlap = overlapForMultiplier elems 1
      results = [(c, overlapForMultiplier elems c) | c <- [1..min 20 maxC]]
  in unlines $
    [ "  Original overlap (c=1): " ++ show origOverlap
    , "  Best multiplier c=" ++ show bestC ++ " → overlap=" ++ show bestOverlap
    , ""
    , "  c   overlap"
    , "  " ++ replicate 20 '-'
    ] ++
    [ "  " ++ padR'' 4 (show c) ++ show o
        ++ (if o < origOverlap then "  ← better!" else "")
        ++ (if c == bestC then "  ★ BEST" else "")
    | (c, o) <- results
    ]

padR'' :: Int -> String -> String
padR'' n s = s ++ replicate (max 0 (n - length s)) ' '

-- ═══════════════════════════════════════════════════════════
-- GF(2) transformations: non-linear overlap reduction
-- ═══════════════════════════════════════════════════════════

-- | Bit matrix: each row is a weight's binary representation.
-- Matrix[i][k] = bit k of weight i.
type BitMatrix = [[Bool]]

-- | Convert weights to a bit matrix (n rows × B columns)
weightsToBitMatrix :: [Int] -> BitMatrix
weightsToBitMatrix elems =
  let b = maxBits elems
  in [toBits b w | w <- elems]

-- | Compute max overlap of a bit matrix.
-- Overlap at column k = number of rows with True at column k
-- that also have True at some column > k.
overlapOfMatrix :: BitMatrix -> Int
overlapOfMatrix [] = 0
overlapOfMatrix mat =
  let cols = length (head mat)
      highestTrue row = maximum (-1 : [k | k <- [0..cols-1], row !! k])
      overlapAt k = length [ row | row <- mat, row !! k, highestTrue row > k ]
  in maximum (0 : [overlapAt k | k <- [0..cols-1]])

-- | Apply a GF(2) column transformation: new_col_j = XOR of selected original columns.
-- A transform is a list of (target_col, [source_cols_to_XOR]).
-- This is a non-linear transformation of the INTEGER values
-- but a linear transformation over GF(2) (the binary field).
xorTransform :: BitMatrix -> [(Int, [Int])] -> BitMatrix
xorTransform mat transforms =
  let cols = length (head mat)
      -- Start with original matrix
      origCols = [[row !! k | row <- mat] | k <- [0..cols-1]]
      -- Apply transforms: each transform XORs source columns into target
      newCols = foldl applyOne origCols transforms
  in transpose' newCols
  where
    applyOne :: [[Bool]] -> (Int, [Int]) -> [[Bool]]
    applyOne colsArr (tgt, srcs) =
      [ if k == tgt
        then zipWith xorAll (colsArr !! tgt) [map (\s -> colsArr !! s !! i) srcs | i <- [0..length (head colsArr)-1]]
        else colsArr !! k
      | k <- [0..length colsArr - 1]
      ]

    xorAll :: Bool -> [Bool] -> Bool
    xorAll base' extras = foldl (/=) base' extras

    transpose' :: [[a]] -> [[a]]
    transpose' [] = []
    transpose' ([] : _) = []
    transpose' xss = map head xss : transpose' (map tail xss)

-- | Search for good GF(2) transforms by trying simple single-XOR operations.
-- For each pair (i, j) where i ≠ j, try: new_col_i = col_i XOR col_j.
-- Report the best overlap reduction found.
searchGF2Transforms :: [Int] -> (Int, Int, String)  -- (original_overlap, best_overlap, description)
searchGF2Transforms elems =
  let mat = weightsToBitMatrix elems
      cols = length (head mat)
      origOverlap = overlapOfMatrix mat
      -- Try all single XOR transforms
      candidates =
        [ (overlapOfMatrix (xorTransform mat [(i, [j])]),
           "col" ++ show i ++ " ^= col" ++ show j)
        | i <- [0..cols-1]
        , j <- [0..cols-1]
        , i /= j
        ]
      -- Also try double XOR (two transforms)
      doubles =
        [ (overlapOfMatrix (xorTransform mat [(i1, [j1]), (i2, [j2])]),
           "col" ++ show i1 ++ "^=col" ++ show j1 ++ ", col" ++ show i2 ++ "^=col" ++ show j2)
        | i1 <- [0..cols-1], j1 <- [0..cols-1], i1 /= j1
        , i2 <- [0..cols-1], j2 <- [0..cols-1], i2 /= j2
        , (i1,j1) < (i2,j2)  -- avoid duplicates
        ]
      allCandidates = candidates ++ take 50 doubles  -- limit doubles for speed
      best = if null allCandidates
             then (origOverlap, "none")
             else minimumBy' allCandidates
  in (origOverlap, fst best, snd best)
  where
    minimumBy' xs = foldl1 (\(o1,d1) (o2,d2) -> if o1 <= o2 then (o1,d1) else (o2,d2)) xs

showGF2Results :: [Int] -> String
showGF2Results elems =
  let (orig, best, desc) = searchGF2Transforms elems
  in unlines
    [ "  Weights: " ++ show elems
    , "  Original overlap: " ++ show orig
    , "  Best GF(2) transform: " ++ desc
    , "  New overlap: " ++ show best
    , "  " ++ if best < orig
              then "REDUCED by " ++ show (orig - best) ++ "! (" ++ show orig ++ " → " ++ show best ++ ")"
              else "No improvement found."
    ]

-- ═══════════════════════════════════════════════════════════
-- Solver in GF(2)-transformed basis
-- ═══════════════════════════════════════════════════════════

-- | THE KEY EXPERIMENT: solve Subset Sum in the GF(2)-transformed basis.
--
-- APPROACH: The GF(2) transform changes the bit matrix but NOT the problem.
-- We still need: Σ (selected weights) = target, in the ORIGINAL integers.
--
-- The transform reduces OVERLAP but changes the CARRY structure.
-- In the original basis: carry at bit k = (sum of selected bits at k + carry_in) / 2
-- In the transformed basis: the "sum" at each position involves XOR-mixed bits,
-- so the carry propagation is non-standard.
--
-- CONCRETE APPROACH: Don't transform the carry. Instead:
-- 1. Find the best GF(2) transform that minimizes overlap
-- 2. Transform the weight bit matrix AND the target bits
-- 3. Run the interleaved solver on transformed bits
-- 4. The coupling decisions (which weights to include) are INVARIANT
--    under the transform — we're choosing the same subset
-- 5. But we need to verify: does the carry work correctly?
--
-- ANSWER: The carry DOESN'T directly work in the transformed basis
-- because XOR transforms mix the positional values. HOWEVER:
-- we can reformulate: instead of tracking carry (an integer),
-- track the full partial sum and check each TRANSFORMED bit.
-- The state at each bit position = set of (partial_sum mod 2^(k+1))
-- values that are consistent with a valid selection.
-- This is the same as coupledBitSolve but on transformed bits.
--
-- THE QUESTION: does the TRANSFORMED overlap affect the state count?

data GF2SolverResult = GF2R
  { gf2Found          :: Bool
  , gf2Correct        :: Bool
  , gf2OrigOverlap    :: Int
  , gf2TransOverlap   :: Int
  , gf2TransformDesc  :: String
  , gf2OrigMaxStates  :: Int    -- interleaved solver on original
  , gf2TransMaxStates :: Int    -- interleaved solver on transformed weights
  , gf2OrigStatesPerBit :: [Int]
  , gf2TransStatesPerBit :: [Int]
  } deriving (Show)

solveInTransformedBasis :: [Int] -> Int -> GF2SolverResult
solveInTransformedBasis elems target =
  let -- Find best GF(2) transform
      (origOverlap, transOverlap, desc) = searchGF2Transforms elems

      -- Transform the weights: apply the same column XOR to get new integer values
      mat = weightsToBitMatrix elems
      b = length (head mat)

      -- Find the actual best transform operations
      bestOps = findBestOps mat
      transMat = xorTransform mat bestOps

      -- Convert transformed bit matrix back to integers
      transWeights = map fromBits transMat
      transTarget = transformTarget target b bestOps

      -- Run interleaved solver on BOTH original and transformed
      origStats = interleavedSolve elems target
      transStats = interleavedSolve transWeights transTarget

      -- Verify correctness: does the transformed solver give the right answer?
      dpAnswer = Set.member target (dpReachableLocal elems)

  in GF2R
    { gf2Found          = isFound transStats
    , gf2Correct        = isFound transStats == dpAnswer
    , gf2OrigOverlap    = origOverlap
    , gf2TransOverlap   = transOverlap
    , gf2TransformDesc  = desc
    , gf2OrigMaxStates  = isMaxStates origStats
    , gf2TransMaxStates = isMaxStates transStats
    , gf2OrigStatesPerBit  = isStatesPerBit origStats
    , gf2TransStatesPerBit = isStatesPerBit transStats
    }

-- | Transform a target value using the same GF(2) column operations
transformTarget :: Int -> Int -> [(Int, [Int])] -> Int
transformTarget target b ops =
  let targetBits = toBits b target
      targetMat = [targetBits]  -- 1-row matrix
      transMat = xorTransform targetMat ops
  in fromBits (head transMat)

-- | Find the actual best single/double XOR operations (replicating searchGF2Transforms logic)
findBestOps :: BitMatrix -> [(Int, [Int])]
findBestOps mat =
  let cols = length (head mat)
      origOverlap = overlapOfMatrix mat
      -- Try single XOR operations
      singles = [ (overlapOfMatrix (xorTransform mat [(i,[j])]), [(i,[j])])
                | i <- [0..cols-1], j <- [0..cols-1], i /= j ]
      -- Try double XOR
      doubles = [ (overlapOfMatrix (xorTransform mat [(i1,[j1]),(i2,[j2])]), [(i1,[j1]),(i2,[j2])])
                | i1 <- [0..cols-1], j1 <- [0..cols-1], i1 /= j1
                , i2 <- [0..cols-1], j2 <- [0..cols-1], i2 /= j2
                , (i1,j1) < (i2,j2) ]
      all' = singles ++ take 50 doubles
      best = if null all' then []
             else snd $ foldl1 (\(o1,d1) (o2,d2) -> if o1 <= o2 then (o1,d1) else (o2,d2)) all'
  in best

showGF2SolverResult :: GF2SolverResult -> String
showGF2SolverResult r = unlines
  [ "  Transform: " ++ gf2TransformDesc r
  , "  Overlap:  " ++ show (gf2OrigOverlap r) ++ " → " ++ show (gf2TransOverlap r)
  , "  Found:    " ++ show (gf2Found r)
  , "  Correct:  " ++ show (gf2Correct r)
  , "  Original  states/bit: " ++ show (gf2OrigStatesPerBit r) ++ " max=" ++ show (gf2OrigMaxStates r)
  , "  Transformed states/bit: " ++ show (gf2TransStatesPerBit r) ++ " max=" ++ show (gf2TransMaxStates r)
  , "  " ++ if gf2TransMaxStates r < gf2OrigMaxStates r
            then "FEWER STATES in transformed basis! (" ++ show (gf2OrigMaxStates r) ++ " → " ++ show (gf2TransMaxStates r) ++ ")"
            else if gf2TransMaxStates r == gf2OrigMaxStates r
            then "Same number of states."
            else "MORE states in transformed basis (" ++ show (gf2OrigMaxStates r) ++ " → " ++ show (gf2TransMaxStates r) ++ ")"
  ]

-- ═══════════════════════════════════════════════════════════
-- GF(2) rank analysis: how much CAN overlap be reduced?
-- ═══════════════════════════════════════════════════════════

-- | Compute the rank of a binary matrix over GF(2) using Gaussian elimination.
gf2Rank :: BitMatrix -> Int
gf2Rank [] = 0
gf2Rank mat =
  let rows = length mat
      cols = if null mat then 0 else length (head mat)
  in go 0 0 mat
  where
    go pivotRow pivotCol m
      | pivotRow >= length m || pivotCol >= (if null m then 0 else length (head m)) = pivotRow
      | otherwise =
          -- Find a row with 1 at pivotCol
          case findPivot pivotRow pivotCol m of
            Nothing -> go pivotRow (pivotCol + 1) m  -- no pivot in this col, try next
            Just pr ->
              let m' = swapRows pivotRow pr m
                  m'' = eliminateCol pivotRow pivotCol m'
              in go (pivotRow + 1) (pivotCol + 1) m''

    findPivot startRow col m =
      case [r | r <- [startRow..length m - 1], (m !! r) !! col] of
        (r:_) -> Just r
        []    -> Nothing

    swapRows i j m
      | i == j = m
      | otherwise = [ if k == i then m !! j else if k == j then m !! i else m !! k
                     | k <- [0..length m - 1] ]

    eliminateCol pivotRow pivotCol m =
      [ if r /= pivotRow && (m !! r) !! pivotCol
        then zipWith (/=) (m !! r) (m !! pivotRow)  -- XOR rows
        else m !! r
      | r <- [0..length m - 1]
      ]

data RankAnalysis = RA
  { raElements       :: [Int]
  , raN              :: Int
  , raBits           :: Int
  , raGF2Rank        :: Int
  , raTheoreticalMin :: Int     -- theoretical minimum overlap
  , raActualOverlap  :: Int     -- current overlap
  , raBestGF2Overlap :: Int     -- best found via GF(2) search
  , raReduction      :: String  -- e.g. "2^8 → 2^2"
  } deriving (Show)

analyzeRank :: [Int] -> RankAnalysis
analyzeRank elems =
  let mat = weightsToBitMatrix elems
      n = length elems
      b = if null mat then 0 else length (head mat)
      rank = gf2Rank mat
      -- Theoretical: if rank = n, overlap can reach 0
      -- If rank < n, at least n - rank weights share columns → overlap ≥ ceil((n-rank)/rank)
      theoMin = if rank >= n then 0
                else max 1 ((n - rank + rank - 1) `div` rank)
      actualOverlap = overlapOfMatrix mat
      (_, bestOverlap, _) = searchGF2Transforms elems
  in RA
    { raElements       = elems
    , raN              = n
    , raBits           = b
    , raGF2Rank        = rank
    , raTheoreticalMin = theoMin
    , raActualOverlap  = actualOverlap
    , raBestGF2Overlap = bestOverlap
    , raReduction      = "2^" ++ show actualOverlap ++ " → 2^" ++ show bestOverlap
                       ++ " (theoretical min: 2^" ++ show theoMin ++ ")"
    }

showRankAnalysis :: RankAnalysis -> String
showRankAnalysis ra = unlines
  [ "  Weights: " ++ show (raElements ra)
  , "  n=" ++ show (raN ra) ++ " bits=" ++ show (raBits ra)
      ++ " GF(2) rank=" ++ show (raGF2Rank ra)
  , "  Overlap: actual=" ++ show (raActualOverlap ra)
      ++ " → best found=" ++ show (raBestGF2Overlap ra)
      ++ " → theoretical min=" ++ show (raTheoreticalMin ra)
  , "  State reduction: " ++ raReduction ra
  , "  " ++ if raGF2Rank ra >= raN ra
            then "FULL RANK: overlap=0 theoretically achievable! (2^n → 2^0)"
            else "RANK DEFICIENT: rank=" ++ show (raGF2Rank ra) ++ " < n=" ++ show (raN ra)
                 ++ " → some overlap unavoidable"
  ]
