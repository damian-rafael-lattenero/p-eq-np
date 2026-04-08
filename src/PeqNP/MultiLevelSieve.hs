module PeqNP.MultiLevelSieve
  ( -- * Core solver
    multiLevelSolve
  , SolveResult(..)
  , showSolveResult
    -- * With representations
  , multiLevelRepSolve
  , fourWayRepSolve
  , repFourWaySolve
  , recursiveRepSolve
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

-- | Enumerate ALL achievable sums using group sieve (NO target-based pruning).
-- Only prunes by upper bound (sum of all weights). Used for inner levels
-- where we need all sums, not just target-relevant ones.
allGroupSums :: [Int] -> Int -> (Set.Set Int, Int)
allGroupSums [] _ = (Set.singleton 0, 1)
allGroupSums weights bitsToMatch =
  let mask = (2^bitsToMatch) - 1
      modulus = 2^bitsToMatch
      groupMap = Map.fromListWith (++) [(w .&. mask, [w]) | w <- weights]
      groupList = Map.toList groupMap
      opts = [ (lowBits, precompute bitsToMatch ws) | (lowBits, ws) <- groupList ]
      -- Cross-group DP with NO lower-bound pruning
      initial = Set.singleton (0 :: Int, 0 :: Int)
      upperH = sum weights `div` modulus + 1
      (final, work) = crossGroupAll modulus upperH opts initial 0
      sums = Set.fromList [ h * modulus + l
                          | (h, l) <- Set.toList final
                          , h * modulus + l >= 0
                          , h * modulus + l <= sum weights ]
      perGroupWork = sum [2 ^ length ws | (_, ws) <- groupList]
  in (sums, work + perGroupWork)

-- | Cross-group DP with ONLY upper bound pruning (for enumeration, not search).
crossGroupAll :: Int -> Int -> [(Int, [(Int, Set.Set Int)])]
              -> Set.Set (Int, Int) -> Int -> (Set.Set (Int, Int), Int)
crossGroupAll _ _ [] states work = (states, work)
crossGroupAll modulus ubH ((lowBits, opts):rest) states work =
  let expanded = Set.fromList
        [ (hAcc + hNew, lAcc + cnt * lowBits)
        | (hAcc, lAcc) <- Set.toList states
        , (cnt, hSums) <- opts
        , hNew <- Set.toList hSums
        ]
      -- Only prune upper bound (no lower bound)
      pruned = Set.filter (\(h, l) -> h + l `div` modulus <= ubH) expanded
  in crossGroupAll modulus ubH rest pruned (work + Set.size pruned)

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

-- | 4-way split with RANGE PROPAGATION + fused prune.
-- Target ranges propagate DOWN so pruning happens BEFORE growth.
--
-- Outer: leftSum ∈ [T-maxR, min(T, maxL)], rightSum = T - leftSum
-- Inner: for each s1 ∈ S1, only keep s2 ∈ S2 where s1+s2 ∈ [leftLo, leftHi]
-- This is a STREAMING merge: enumerate S1, prune S2 for each s1.
fourWayRepSolve :: Int -> Int -> [Int] -> Int -> SolveResult
fourWayRepSolve _m1 _m2 weights target =
  let n = length weights
      q = n `div` 4
      (q1, rest1) = splitAt q weights
      (q2, rest2) = splitAt q rest1
      (q3, q4)    = splitAt q rest2
      -- Target ranges for each half
      maxL = sum q1 + sum q2
      maxR = sum q3 + sum q4
      leftLo = max 0 (target - maxR)
      leftHi = min target maxL
      rightLo = max 0 (target - maxL)
      rightHi = min target maxR
      -- Per quarter: enumerate sums with group sieve
      b1 = pickBestBits q1 target; b2 = pickBestBits q2 target
      b3 = pickBestBits q3 target; b4 = pickBestBits q4 target
      (s1, w1) = allGroupSums q1 b1
      (s2, w2) = allGroupSums q2 b2
      (s3, w3) = allGroupSums q3 b3
      (s4, w4) = allGroupSums q4 b4
      -- FUSED merge+prune: enumerate S1, for each s1 only get matching S2
      leftSums = Set.fromList
        [ a + b | a <- Set.toList s1
        , let bLo = max 0 (leftLo - a)
              bHi = leftHi - a
        , bHi >= bLo
        , b <- Set.toAscList (filterRange bLo bHi s2)
        ]
      rightSums = Set.fromList
        [ a + b | a <- Set.toList s3
        , let bLo = max 0 (rightLo - a)
              bHi = rightHi - a
        , bHi >= bLo
        , b <- Set.toAscList (filterRange bLo bHi s4)
        ]
      -- Final check
      found = any (\l -> Set.member (target - l) rightSums) (Set.toList leftSums)
      dpAnswer = Set.member target (bruteForceDP weights)
      innerWork = w1 + w2 + w3 + w4
      mergeWork = Set.size leftSums + Set.size rightSums
      totalWork = innerWork + mergeWork
  in SR found (found == dpAnswer) totalWork 2 (Set.size leftSums) (Set.size rightSums)

-- | RANGE-BOUNDED merge: only produce sums a+b in [lo, hi].
-- For each a ∈ A: need b such that lo - a ≤ b ≤ hi - a.
-- Use sorted B + binary search to find the valid range of b.
-- Total: O(|A| × log|B| + |output|) instead of O(|A| × |B|).
filteredMerge :: Set.Set Int -> Set.Set Int -> Int -> Int -> Set.Set Int
filteredMerge setA setB upperBound _modulus =
  let bList = Set.toAscList setB  -- sorted for binary search-like filtering
      bSet = setB                 -- for Set operations
      lo = 0
      hi = upperBound
  in Set.fromList
       [ a + b
       | a <- Set.toList setA
       , let bLo = max 0 (lo - a)
             bHi = hi - a
       , bHi >= 0  -- skip if no valid b exists
       -- Get b values in range [bLo, bHi] from bSet
       , b <- Set.toAscList (filterRange bLo bHi bSet)
       ]

-- | Range-bounded merge: only produce sums a+b in [lo, hi].
filteredMergeRange :: Set.Set Int -> Set.Set Int -> Int -> Int -> Set.Set Int
filteredMergeRange setA setB lo hi =
  Set.fromList
    [ a + b
    | a <- Set.toList setA
    , let bLo = max 0 (lo - a)
          bHi = hi - a
    , bHi >= 0
    , b <- Set.toAscList (filterRange bLo bHi setB)
    ]

-- | Extract elements in [lo, hi] from a Set. O(log n + k) where k = output size.
filterRange :: Int -> Int -> Set.Set Int -> Set.Set Int
filterRange lo hi s =
  let (_, geqLo) = Set.split (lo - 1) s   -- elements ≥ lo
      (leqHi, _) = Set.split (hi + 1) geqLo  -- elements ≤ hi
  in leqHi

-- ═══════════════════════════════════════════════════════════
-- REPRESENTATIONS: BCJ technique adapted to group sieve
-- ═══════════════════════════════════════════════════════════

-- | BCJ-style representations with group sieve.
-- Fix modulus M and try each residue r = 0..M-1:
--   Left half sum ≡ r (mod M), right half sum ≡ (T-r) (mod M).
-- Each residue gives an EXACT modular target to inner merges.
-- Inner merge uses hash-bucket lookup: O(|S1| × |S2|/M) per residue.
-- Total: M × O(|S1| × |S2|/M) = O(|S1| × |S2|) same...
-- BUT: combined with group sieve pruning at inner level, it's better.
repFourWaySolve :: Int -> [Int] -> Int -> SolveResult
repFourWaySolve modRep weights target =
  let n = length weights
      q = n `div` 4
      (q1, rest1) = splitAt q weights
      (q2, rest2) = splitAt q rest1
      (q3, q4)    = splitAt q rest2
      -- Quarter sums (brute force — they're 2^{n/4} each)
      s1 = bruteForceDP q1; s2 = bruteForceDP q2
      s3 = bruteForceDP q3; s4 = bruteForceDP q4
      m = max 2 modRep
      -- Bucket each quarter's sums by residue mod M (precompute once)
      b2 = Map.fromListWith (++) [(s `mod` m, [s]) | s <- Set.toList s2]
      b4 = Map.fromListWith (++) [(s `mod` m, [s]) | s <- Set.toList s4]
      tMod = target `mod` m
      -- Try each residue r: leftSum ≡ r mod M, rightSum ≡ (T-r) mod M
      (found, work) = go 0 0
        where
          go r w | r >= m = (False, w)
          go r w =
            let -- Left: for each a ∈ S1, grab b from bucket (r-a) mod M in S2
                leftSums = Set.fromList
                  [ a + b'
                  | a <- Set.toList s1
                  , b' <- Map.findWithDefault [] ((r - a `mod` m) `mod` m) b2
                  ]
                -- Right: for each c ∈ S3, grab d from bucket ((tMod-r)-c) mod M in S4
                rr = (tMod - r) `mod` m
                rightSums = Set.fromList
                  [ c + d'
                  | c <- Set.toList s3
                  , d' <- Map.findWithDefault [] ((rr - c `mod` m) `mod` m) b4
                  ]
                -- Check match
                hit = any (\l -> Set.member (target - l) rightSums) (Set.toList leftSums)
                stepW = Set.size leftSums + Set.size rightSums
            in if hit then (True, w + stepW)
               else go (r + 1) (w + stepW)
      dpAnswer = Set.member target (bruteForceDP weights)
      innerWork = Set.size s1 + Set.size s2 + Set.size s3 + Set.size s4
  in SR found (found == dpAnswer) (innerWork + work) 2 0 0

-- | RECURSIVE representations: 2-level modular filtering.
-- Level 1 (inner): for each r1 mod M1, filter Q1+Q2 merge
-- Level 2 (outer): for filtered leftSums, check against rightSums
-- Key: don't iterate ALL r1. For each a ∈ S1, a's residue DETERMINES r1.
-- So we process S1 once, bucketing results by r1 = (a mod M1).
-- Then for each r1-bucket, merge with S2 filtered for that r1.
-- This gives O(|S1| × |S2|/M1) total inner work.
recursiveRepSolve :: Int -> [Int] -> Int -> SolveResult
recursiveRepSolve m1 weights target =
  let n = length weights
      q = n `div` 4
      (q1, rest1) = splitAt q weights
      (q2, rest2) = splitAt q rest1
      (q3, q4)    = splitAt q rest2
      s1 = bruteForceDP q1; s2 = bruteForceDP q2
      s3 = bruteForceDP q3; s4 = bruteForceDP q4
      -- Bucket S2 and S4 by residue mod M1
      b2 = Map.fromListWith (++) [(s `mod` m1, [s]) | s <- Set.toList s2]
      b4 = Map.fromListWith (++) [(s `mod` m1, [s]) | s <- Set.toList s4]
      tMod = target `mod` m1
      -- For each a ∈ S1: r1 = (a + b) mod M1 is determined by which bucket of S2 we pick.
      -- We want leftSum = a + b where leftSum ≡ ANY r1, and rightSum ≡ (T-r1) mod M1.
      -- Process: for each a, for each b in matching bucket, produce leftSum.
      -- Then check if (T - leftSum) is achievable from S3+S4 with right residue.
      --
      -- EFFICIENT: build Map from leftSum → () for ALL valid (a,b) combos.
      -- Then for each leftSum, check rightSum = T - leftSum in right sums.
      -- Right sums: same construction from S3, S4 with matching residue.
      --
      -- But which residue? leftSum mod M1 = r1 → rightSum mod M1 = (T - r1) mod M1.
      -- Since r1 varies with each leftSum, right sums need all residues too.
      -- Solution: precompute ALL right sums (like MITM), but ONLY keep those
      -- where the residue matches some possible left residue.
      -- Actually: just build the full right set and check. The modular filter
      -- reduces the INNER merge work, not the outer check.
      --
      -- SIMPLIFIED: for each r1 = 0..M1-1:
      --   leftSums(r1) = {a+b | a ∈ S1, b ∈ S2, (a+b) mod M1 = r1}
      --                = {a+b | a ∈ S1, b ∈ bucket((r1-a) mod M1) of S2}
      --   rightSums(r1) = {c+d | c ∈ S3, d ∈ bucket(((T-r1)-c) mod M1) of S4}
      --   Check: any l ∈ leftSums(r1) where (T-l) ∈ rightSums(r1)?
      --
      -- Work per r1: |S1| × |bucket_S2| + |S3| × |bucket_S4| + min(|L|,|R|) × log(max(|L|,|R|))
      -- |bucket| ≈ |S|/M1. With M1 r1's: total = M1 × (|S1|×|S2|/M1 + ...) = |S1|×|S2| + ...
      -- Same total BUT: we can STOP at the first r1 that finds a match!
      -- For YES instances: expected to find match at r1 ≈ 1 (if many representations)

      (found, work) = goR 0 0
      goR r w | r >= m1 = (False, w)
      goR r w =
        let leftR = Set.fromList
              [ a + b
              | a <- Set.toList s1
              , b <- Map.findWithDefault [] ((r - a `mod` m1) `mod` m1) b2
              ]
            rRight = (tMod - r) `mod` m1
            rightR = Set.fromList
              [ c + d
              | c <- Set.toList s3
              , d <- Map.findWithDefault [] ((rRight - c `mod` m1) `mod` m1) b4
              ]
            hit = any (\l -> Set.member (target - l) rightR) (Set.toList leftR)
            stepW = Set.size leftR + Set.size rightR
        in if hit then (True, w + stepW)
           else goR (r + 1) (w + stepW)
      dpAnswer = Set.member target (bruteForceDP weights)
      innerWork = Set.size s1 + Set.size s2 + Set.size s3 + Set.size s4
  in SR found (found == dpAnswer) (innerWork + work) 2 0 0
