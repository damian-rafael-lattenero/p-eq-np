module PeqNP.Topological
  ( GapAnalysis(..)
  , analyzeGaps
  , gapPeriodicity
  , showGapAnalysis
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import Data.List (group, sort, maximumBy)
import Data.Ord (comparing)

import PeqNP.DPSolver (dpReachable)

-- | Topological analysis of the reachable sum space.
--
-- The set S = {reachable sums} ⊂ [0, Σwi] has "gaps" (unreachable sums).
-- The STRUCTURE of these gaps is a non-algebraic property —
-- it doesn't extend to algebraic closures, making it a candidate
-- for a non-algebrizing approach.
data GapAnalysis = GA
  { gaElements     :: [Int]
  , gaReachableCount :: Int
  , gaTotalRange   :: Int
  , gaGapCount     :: Int
  , gaGapRuns      :: [Int]     -- sizes of consecutive gap runs
  , gaMaxGapRun    :: Int
  , gaGapDensity   :: Double    -- fraction of range that are gaps
  , gaPeriod       :: Maybe Int -- detected periodicity in gaps
  } deriving (Show)

analyzeGaps :: [Int] -> GapAnalysis
analyzeGaps elems =
  let reachable = dpReachable elems
      totalSum = sum elems
      allInRange = Set.fromList [0..totalSum]
      gaps = Set.difference allInRange reachable
      gapList = Set.toAscList gaps
      -- Compute runs of consecutive gaps
      runs = if null gapList then []
             else computeRuns gapList
      period = gapPeriodicity gapList
  in GA
    { gaElements       = elems
    , gaReachableCount = Set.size reachable
    , gaTotalRange     = totalSum + 1
    , gaGapCount       = Set.size gaps
    , gaGapRuns        = runs
    , gaMaxGapRun      = if null runs then 0 else maximum runs
    , gaGapDensity     = fromIntegral (Set.size gaps) / fromIntegral (max 1 (totalSum + 1))
    , gaPeriod         = period
    }

computeRuns :: [Int] -> [Int]
computeRuns [] = []
computeRuns (x:xs) = go 1 x xs
  where
    go len prev [] = [len]
    go len prev (y:ys)
      | y == prev + 1 = go (len + 1) y ys
      | otherwise      = len : go 1 y ys

-- | Detect periodicity in gap positions.
-- Compute differences between consecutive gaps. If most differences
-- are the same value d, the gaps are periodic with period d.
gapPeriodicity :: [Int] -> Maybe Int
gapPeriodicity gaps
  | length gaps < 3 = Nothing
  | otherwise =
      let diffs = zipWith (-) (tail gaps) gaps
          grouped = group (sort diffs)
          mostCommon = maximumBy (comparing length) grouped
          freq = length mostCommon
          total = length diffs
      in if freq * 3 > total * 2  -- >66% same difference → periodic
         then Just (head mostCommon)
         else Nothing

showGapAnalysis :: GapAnalysis -> String
showGapAnalysis ga = unlines
  [ "  Elements: " ++ show (gaElements ga)
  , "  Reachable: " ++ show (gaReachableCount ga) ++ " / " ++ show (gaTotalRange ga)
  , "  Gaps: " ++ show (gaGapCount ga)
      ++ " (" ++ show (round' 1 (gaGapDensity ga * 100)) ++ "% of range)"
  , "  Max gap run: " ++ show (gaMaxGapRun ga)
  , "  Period: " ++ maybe "none detected" show (gaPeriod ga)
  ]
  where round' n x = fromIntegral (round (x * 10^(n::Int)) :: Int) / 10^(n::Int)
