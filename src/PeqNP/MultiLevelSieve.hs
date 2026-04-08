module PeqNP.MultiLevelSieve
  ( -- * Core solver
    multiLevelSolve
  , SolveResult(..)
  , showSolveResult
    -- * Pruned group sieve (inner level)
  , prunedGroupSums
    -- * Benchmarking
  , benchmark
  , BenchResult(..)
  , showBenchmark
    -- * Density-1 instance generator
  , mkDensity1
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
-- using group sieve with cross-group pruning.
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
      -- Pruned cross-group DP
      initial = Set.singleton (0 :: Int, 0 :: Int)
      (final, work) = crossGroupDP modulus (upperBound `div` modulus)
                                   opts maxHighPerGroup initial 0
      -- Convert states to actual sums
      sums = Set.fromList [ h * modulus + l
                          | (h, l) <- Set.toList final
                          , let s = h * modulus + l
                          , s >= 0, s <= upperBound ]
      perGroupWork = sum [2 ^ length ws | (_, ws) <- groupList]
  in (sums, work + perGroupWork)

precompute :: Int -> [Int] -> [(Int, Set.Set Int)]
precompute b ws =
  let highParts = map (\w -> w `div` (2^b)) ws
      allSubs = [(length sel, sum sel) | sel <- subsequences highParts]
      grouped = Map.fromListWith Set.union
                  [(cnt, Set.singleton s) | (cnt, s) <- allSubs]
  in Map.toList grouped

crossGroupDP :: Int -> Int -> [(Int, [(Int, Set.Set Int)])] -> [Int]
             -> Set.Set (Int, Int) -> Int -> (Set.Set (Int, Int), Int)
crossGroupDP _ _ [] _ states work = (states, work)
crossGroupDP modulus ubHigh ((lowBits, opts):rest) (maxH:maxHRest) states work =
  let -- Expand by all group options
      expanded = Set.fromList
        [ (hAcc + hNew, lAcc + cnt * lowBits)
        | (hAcc, lAcc) <- Set.toList states
        , (cnt, hSums) <- opts
        , hNew <- Set.toList hSums
        ]
      -- Prune: discard states that can't reach target range
      remainingMaxH = sum maxHRest
      pruned = Set.filter (\(h, l) ->
        let currentH = h + l `div` modulus
        in currentH <= ubHigh && currentH + remainingMaxH >= 0
        ) expanded
  in crossGroupDP modulus ubHigh rest maxHRest pruned (work + Set.size pruned)
crossGroupDP _ _ _ [] states work = (states, work)

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
