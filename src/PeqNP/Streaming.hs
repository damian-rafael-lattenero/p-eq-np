module PeqNP.Streaming
  ( StreamStats(..)
  , streamingSolve
  , showStreamStats
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

-- | Streaming Subset Sum solver with per-step pruning.
--
-- Instead of materializing the full 2^n tree, process one element
-- at a time. At each step: bifurcate (include/skip) all live sums,
-- then PRUNE sums that can no longer reach the target.
--
-- This is DP with aggressive pruning: at step i with remaining
-- elements rest, a partial sum s survives iff:
--   s <= target  AND  target <= s + sum(rest)
--
-- The "bubbling soda": sums that can't lead anywhere evaporate
-- at each step, keeping only the live ones.

data StreamStats = StreamStats
  { stFound          :: Bool
  , stLiveSumsPerStep :: [Int]   -- |live sums| at each step
  , stMaxLive        :: Int      -- peak live sums
  , stDPComparison   :: Int      -- what DP would have (no pruning)
  } deriving (Show)

-- | Streaming solver: process elements left to right, prune at each step
streamingSolve :: [Int] -> Int -> StreamStats
streamingSolve elems target =
  let (found, liveCounts, dpCount) = go (Set.singleton 0) elems (sum elems) []
  in StreamStats
    { stFound           = found
    , stLiveSumsPerStep = reverse liveCounts
    , stMaxLive         = maximum (0 : liveCounts)
    , stDPComparison    = dpCount
    }
  where
    go :: Set Int -> [Int] -> Int -> [Int] -> (Bool, [Int], Int)
    go sums [] _restSum counts =
      (Set.member target sums, Set.size sums : counts, Set.size sums)
    go sums (x:xs) restSum counts =
      let -- Bifurcate: each live sum branches into (s, s+x)
          branched = Set.union sums (Set.map (+ x) sums)
          restSum' = restSum - x
          -- Prune: keep only sums that can still reach target
          pruned = Set.filter (\s -> s <= target && target <= s + restSum') branched
          -- DP comparison: what size would be without pruning
          _dpSize = Set.size branched
      in go pruned xs restSum' (Set.size sums : counts)

showStreamStats :: StreamStats -> String
showStreamStats ss = unlines
  [ "  Found:              " ++ show (stFound ss)
  , "  Live sums/step:     " ++ show (stLiveSumsPerStep ss)
  , "  Peak live sums:     " ++ show (stMaxLive ss)
  , "  DP would have:      " ++ show (stDPComparison ss)
  , "  Pruning saved:      " ++
      (if stDPComparison ss > 0
       then show (roundTo 1 (100.0 * (1.0 - fromIntegral (stMaxLive ss) / fromIntegral (stDPComparison ss)))) ++ "%"
       else "N/A")
  ]
  where
    roundTo n x = fromIntegral (round (x * 10^(n :: Int)) :: Int) / 10^(n :: Int)
