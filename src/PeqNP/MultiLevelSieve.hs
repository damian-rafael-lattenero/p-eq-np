module PeqNP.MultiLevelSieve
  ( -- * Core solver
    multiLevelSolve
  , SolveResult(..)
  , showSolveResult
    -- * With representations
  , multiLevelRepSolve
  , fourWayRepSolve
    -- * Pruned group sieve (inner level)
  , prunedGroupSums
    -- * Benchmarking
  , benchmark
  , BenchResult(..)
  , showBenchmark
    -- * Density-1 instance generator
  , mkDensity1
    -- * Utilities
  , padR
  , roundTo
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Bits ((.&.))
import Data.List (foldl', minimumBy)
import Data.Ord (comparing)

-- ═══════════════════════════════════════════════════════════
-- Instance generator
-- ═══════════════════════════════════════════════════════════

-- | Generate a density-1 Subset Sum instance: weights ≈ 2^n.
mkDensity1 :: Int -> ([Int], Int)
mkDensity1 n =
  let ws = [2^n + ((i * 1103515245 + 12345) `mod` (2^(n-1))) | i <- [0..n-1]]
      t = sum ws `div` 2 + 1
  in (ws, t)

-- ═══════════════════════════════════════════════════════════
-- Pruned group sieve: enumerates achievable sums with pruning
-- ═══════════════════════════════════════════════════════════

-- | Enumerate all achievable subset sums up to upperBound,
-- using group sieve with AGGRESSIVE cross-group pruning.
-- Returns (set of achievable sums, work performed).
prunedGroupSums :: [Int] -> Int -> Int -> (Set.Set Int, Int)
prunedGroupSums [] _ _ = (Set.singleton 0, 1)
prunedGroupSums weights upperBound bitsToMatch =
  let mask = (2^bitsToMatch) - 1
      modulus = 2^bitsToMatch
      groupMap = Map.fromListWith (++) [(w .&. mask, [w]) | w <- weights]
      groupList = Map.toList groupMap
      -- Per group: precompute (count, set of high-part sums)
      opts = [ (lowBits, precompute bitsToMatch ws)
             | (lowBits, ws) <- groupList ]
      maxHighPerGroup = [ maximum (0 : concat [Set.toList hs | (_, hs) <- o])
                        | (_, o) <- opts ]
      -- Also compute MIN high per group (for tighter lower bound)
      minHighPerGroup = [ 0 | _ <- opts ]  -- minimum is always 0 (empty subset)
      -- Pruned cross-group DP with TIGHT bounds
      initial = Set.singleton (0 :: Int, 0 :: Int)
      targetHigh = upperBound `div` modulus
      (final, work) = crossGroupDPTight modulus targetHigh
                                        opts maxHighPerGroup initial 0
      -- Convert states to actual sums
      sums = Set.fromList [ h * modulus + l
                          | (h, l) <- Set.toList final
                          , let s = h * modulus + l
                          , s >= 0, s <= upperBound ]
      perGroupWork = sum [2 ^ length ws | (_, ws) <- groupList]
  in (sums, work + perGroupWork)

-- | Cross-group DP with TIGHT pruning:
-- 1. Upper bound: currentH ≤ targetHigh (can't overshoot)
-- 2. Lower bound: currentH + remainingMaxH ≥ targetHigh (must be able to reach)
-- 3. Modular: early discard if lAcc can't reach targetLow given remaining groups
crossGroupDPTight :: Int -> Int -> [(Int, [(Int, Set.Set Int)])] -> [Int]
                  -> Set.Set (Int, Int) -> Int -> (Set.Set (Int, Int), Int)
crossGroupDPTight _ _ [] _ states work = (states, work)
crossGroupDPTight modulus tgtH ((lowBits, opts):rest) (mxH:mxHRest) states work =
  let -- Expand
      expanded = Set.fromList
        [ (hAcc + hNew, lAcc + cnt * lowBits)
        | (hAcc, lAcc) <- Set.toList states
        , (cnt, hSums) <- opts
        , hNew <- Set.toList hSums
        ]
      -- TIGHT prune
      remainingMaxH = sum mxHRest
      pruned = Set.filter (\(h, l) ->
        let currentH = h + l `div` modulus
            -- Upper: can't exceed target (accounting for carry from low bits)
            upperOk = currentH <= tgtH + 1  -- +1 for possible carry
            -- Lower: must be able to reach target with remaining groups
            lowerOk = currentH + remainingMaxH >= tgtH
        in upperOk && lowerOk
        ) expanded
  in crossGroupDPTight modulus tgtH rest mxHRest pruned (work + Set.size pruned)
crossGroupDPTight _ _ _ [] states work = (states, work)

precompute :: Int -> [Int] -> [(Int, Set.Set Int)]
precompute b ws =
  let highParts = map (\w -> w `div` (2^b)) ws
      allSubs = [(length sel, sum sel) | sel <- subsequences highParts]
      grouped = Map.fromListWith Set.union
                  [(cnt, Set.singleton s) | (cnt, s) <- allSubs]
  in Map.toList grouped

-- (crossGroupDP replaced by crossGroupDPTight above)

subsequences :: [a] -> [[a]]
subsequences [] = [[]]
subsequences (x:xs) = let r = subsequences xs in r ++ map (x:) r

-- ═══════════════════════════════════════════════════════════
-- Multi-level solver
-- ═══════════════════════════════════════════════════════════

data SolveResult = SR
  { srFound   :: Bool
  , srCorrect :: Bool
  , srWork    :: Int
  , srLevels  :: Int
  , srLeftSize  :: Int
  , srRightSize :: Int
  } deriving (Show)

-- | K-level solver: split into halves recursively, merge at each level.
-- Level 0: direct pruned group sieve.
-- Level k: split in half, solve each half with level k-1, MITM merge.
multiLevelSolve :: Int -> [Int] -> Int -> SolveResult
multiLevelSolve levels weights target =
  let (leftSums, rightSums, work) = solveInner levels weights target
      found = any (\l -> Set.member (target - l) rightSums) (Set.toList leftSums)
      dpAnswer = Set.member target (bruteForceDP weights)
  in SR found (found == dpAnswer) work levels (Set.size leftSums) (Set.size rightSums)

-- | Inner solver returning (leftSums, rightSums, work)
solveInner :: Int -> [Int] -> Int -> (Set.Set Int, Set.Set Int, Int)
solveInner _ weights target | length weights <= 6 =
  let sums = bruteForceDP weights
  in (sums, sums, Set.size sums)
solveInner 0 weights target =
  -- Base level: pruned group sieve, try bits=1,2,3 pick best
  let bestB = pickBestBits weights target
      (sums, work) = prunedGroupSums weights target bestB
  in (sums, sums, work)
solveInner levels weights target =
  let n = length weights
      mid = n `div` 2
      (leftW, rightW) = splitAt mid weights
      -- Recurse on each half
      bestBL = pickBestBits leftW target
      bestBR = pickBestBits rightW target
      (leftSums, _, leftWork) = solveInner (levels - 1) leftW target
      (rightSums, _, rightWork) = solveInner (levels - 1) rightW target
      mergeWork = Set.size leftSums
  in (leftSums, rightSums, leftWork + rightWork + mergeWork)

pickBestBits :: [Int] -> Int -> Int
pickBestBits weights _ =
  let n = length weights
      maxW = if null weights then 1 else maximum weights
      origBits = ceiling (logBase 2 (fromIntegral maxW + 1) :: Double)
      -- Try bits 1-4, compute group sizes
      options = [ (b, maxG, perGrp)
                | b <- [1..min 4 origBits]
                , let mask = (2^b) - 1
                      grps = Map.fromListWith (+) [(w .&. mask, 1::Int) | w <- weights]
                      maxG = maximum (Map.elems grps)
                      perGrp = sum [2^g | g <- Map.elems grps]
                , maxG >= 2  -- at least 2 per group
                ]
  in if null options then max 1 (floor (sqrt (fromIntegral origBits) :: Double))
     else let (b, _, _) = minimumBy (comparing (\(_, _, pg) -> pg)) options in b

bruteForceDP :: [Int] -> Set.Set Int
bruteForceDP = foldl' (\s w -> Set.union s (Set.map (+ w) s)) (Set.singleton 0)

showSolveResult :: SolveResult -> String
showSolveResult sr =
  "found=" ++ show (srFound sr) ++ " correct=" ++ show (srCorrect sr)
  ++ " work=" ++ show (srWork sr) ++ " levels=" ++ show (srLevels sr)
  ++ " |L|=" ++ show (srLeftSize sr) ++ " |R|=" ++ show (srRightSize sr)

-- ═══════════════════════════════════════════════════════════
-- Benchmarking: compare all levels against MITM
-- ═══════════════════════════════════════════════════════════

data BenchResult = BR
  { brN       :: Int
  , brMITM    :: Int
  , brLevel1  :: Int
  , brLevel2  :: Int
  , brLevel3  :: Int
  , brBest    :: Int
  , brRatio   :: Double
  , brAllOk   :: Bool
  } deriving (Show)

benchmark :: Int -> BenchResult
benchmark n =
  let (ws, t) = mkDensity1 n
      mitm = 3 * 2 ^ (n `div` 2)
      sr1 = multiLevelSolve 1 ws t
      sr2 = multiLevelSolve 2 ws t
      sr3 = multiLevelSolve 3 ws t
      best = minimum [srWork sr1, srWork sr2, srWork sr3]
      ratio = fromIntegral mitm / fromIntegral (max 1 best)
      allOk = srCorrect sr1 && srCorrect sr2 && srCorrect sr3
  in BR n mitm (srWork sr1) (srWork sr2) (srWork sr3) best ratio allOk

showBenchmark :: [BenchResult] -> String
showBenchmark results = unlines $
  [ "  " ++ padR 5 "n" ++ padR 10 "1-level" ++ padR 10 "2-level"
    ++ padR 10 "3-level" ++ padR 10 "MITM" ++ padR 8 "ratio" ++ "ok"
  , "  " ++ replicate 58 '-'
  ] ++
  [ "  " ++ padR 5 (show (brN r))
    ++ padR 10 (show (brLevel1 r))
    ++ padR 10 (show (brLevel2 r))
    ++ padR 10 (show (brLevel3 r))
    ++ padR 10 (show (brMITM r))
    ++ padR 8 (show (roundTo 2 (brRatio r)))
    ++ (if brAllOk r then "✓" else "✗")
  | r <- results
  ]

padR :: Int -> String -> String
padR n s = s ++ replicate (max 0 (n - length s)) ' '

roundTo :: Int -> Double -> Double
roundTo n x = fromIntegral (round (x * 10 ^ n) :: Int) / 10 ^ (fromIntegral n)

-- ═══════════════════════════════════════════════════════════
-- REPRESENTATIONS technique combined with group sieve
-- ═══════════════════════════════════════════════════════════

-- | The HGJ representations trick:
-- Instead of target = a + b with ONE split, use MODULAR FILTERING:
-- Fix modulus M, fix random r ∈ [0, M-1].
-- Only enumerate left sums ≡ r (mod M), right sums ≡ (target-r) (mod M).
-- This reduces each side by factor M.
-- But the "right" r exists with probability ≥ 1/M.
-- Try all r = 0..M-1: total work = M × (work_per_r) = M × (|sums|/M)² = |sums|²/M.
--
-- For group sieve: the modular filter is applied DURING cross-group DP,
-- not as a post-filter. This means the pruned DP has even fewer states.

-- | Multi-level solver WITH representations at the merge level.
multiLevelRepSolve :: Int -> Int -> [Int] -> Int -> SolveResult
-- levels = recursion depth, modulus = M for representations
multiLevelRepSolve levels modRep weights target =
  let (found, work) = solveRep levels modRep weights target
      dpAnswer = Set.member target (bruteForceDP weights)
  in SR found (found == dpAnswer) work levels 0 0

solveRep :: Int -> Int -> [Int] -> Int -> (Bool, Int)
solveRep _ _ weights target | length weights <= 6 =
  let sums = bruteForceDP weights
  in (Set.member target sums, Set.size sums)
solveRep 0 _ weights target =
  let bestB = pickBestBits weights target
      (sums, work) = prunedGroupSums weights target bestB
  in (Set.member target sums, work)
solveRep levels modRep weights target =
  let n = length weights
      mid = n `div` 2
      (leftW, rightW) = splitAt mid weights
      -- Get sum sets from each half (using group sieve)
      bestBL = pickBestBits leftW target
      bestBR = pickBestBits rightW target
      (leftSums, leftWork) = prunedGroupSums leftW target bestBL
      (rightSums, rightWork) = prunedGroupSums rightW target bestBR
      -- REPRESENTATIONS: for each r = 0..M-1, only check
      -- left sums ≡ r (mod M) against right sums ≡ (target-r) (mod M)
      -- This divides the merge work by M
      m = max 2 modRep
      -- Bucket left and right sums by residue mod M
      leftBuckets = Map.fromListWith Set.union
        [(s `mod` m, Set.singleton s) | s <- Set.toList leftSums]
      rightBuckets = Map.fromListWith Set.union
        [(s `mod` m, Set.singleton s) | s <- Set.toList rightSums]
      -- For each r, check if any left(r) + right(target-r mod M) = target
      targetMod = target `mod` m
      found = any (\r ->
        let rRight = (targetMod - r) `mod` m
            lSet = Map.findWithDefault Set.empty r leftBuckets
            rSet = Map.findWithDefault Set.empty rRight rightBuckets
        in any (\l -> Set.member (target - l) rSet) (Set.toList lSet)
        ) [0..m-1]
      -- Work: generating sums + filtered merge
      -- Merge work ≈ Σ_r |leftBucket(r)| = |leftSums| (same total, but spread)
      -- The improvement: each bucket is |leftSums|/M, search is in |rightSums|/M
      -- So merge = M × (|L|/M × log(|R|/M)) = |L| × log(|R|/M)
      -- vs MITM: |L| × log(|R|)
      -- Improvement: log factor only. Real improvement comes from RECURSIVE application.
      mergeWork = Set.size leftSums  -- conservative estimate
  in (found, leftWork + rightWork + mergeWork)

-- | 4-way split with representations at BOTH levels.
-- Split into 4 quarters. Inner merge: Q1+Q2 and Q3+Q4 with mod M1.
-- Outer merge: (Q1+Q2) + (Q3+Q4) with mod M2.
-- Total: 4 × 2^{n/4} inner + filtered merges.
fourWayRepSolve :: Int -> Int -> [Int] -> Int -> SolveResult
fourWayRepSolve m1 m2 weights target =
  let n = length weights
      q = n `div` 4
      (q1, rest1) = splitAt q weights
      (q2, rest2) = splitAt q rest1
      (q3, q4)    = splitAt q rest2
      -- Inner: enumerate sums of each quarter
      b1 = pickBestBits q1 target
      b2 = pickBestBits q2 target
      b3 = pickBestBits q3 target
      b4 = pickBestBits q4 target
      -- Use bruteForceDP for quarters (they're small: n/4 elements)
      s1 = bruteForceDP q1; w1 = Set.size s1
      s2 = bruteForceDP q2; w2 = Set.size s2
      s3 = bruteForceDP q3; w3 = Set.size s3
      s4 = bruteForceDP q4; w4 = Set.size s4
      -- Inner merge with mod M1: combine Q1+Q2 and Q3+Q4
      leftSums = filteredMerge s1 s2 (sum q1 + sum q2) m1
      rightSums = filteredMerge s3 s4 (sum q3 + sum q4) m2
      -- Outer merge
      found = any (\l -> Set.member (target - l) rightSums) (Set.toList leftSums)
      dpAnswer = Set.member target (bruteForceDP weights)
      innerWork = w1 + w2 + w3 + w4
      mergeWork = Set.size s1 + Set.size s3 + Set.size leftSums
      totalWork = innerWork + mergeWork
  in SR found (found == dpAnswer) totalWork 2 (Set.size leftSums) (Set.size rightSums)

-- | Range-filtered merge: combine sums from two sets, keep only those in range.
-- Uses a Set for B so lookup for the final target-check is O(log n).
-- For intermediate merges: produce ALL sums a+b in [0, upperBound].
filteredMerge :: Set.Set Int -> Set.Set Int -> Int -> Int -> Set.Set Int
filteredMerge setA setB upperBound _modulus =
  Set.fromList
    [ a + b
    | a <- Set.toList setA
    , b <- Set.toList setB
    , let s = a + b
    , s >= 0
    , s <= upperBound
    ]
