module PeqNP.Comparison
  ( ComparisonResult(..)
  , compareApproaches
  , showComparison
  ) where

import qualified Data.Map.Strict as Map
import Data.List (sort)

import PeqNP.BruteForce (allPaths, solveBruteForce)
import PeqNP.DPSolver (dpTable, solveDPAll)

-- | Side-by-side comparison of brute force and DP approaches.
--
-- THE KEY DEMONSTRATION:
-- Both approaches answer the same question, but brute force explores
-- the full hom-object (2^n paths) while DP works on the quotiented
-- hom-object (at most O(n * max_sum) equivalence classes).
-- The comparison proves they agree, and shows the compression ratio.

data ComparisonResult = CR
  { bfSolutions :: [[Int]]    -- ^ Solutions from brute force
  , dpSolutions :: [[Int]]    -- ^ Solutions from DP
  , bfPathCount :: Int        -- ^ Total paths explored (2^n)
  , dpClassCount :: Int       -- ^ Equivalence classes in DP table
  , agree :: Bool             -- ^ Do both approaches agree?
  } deriving (Show)

-- | Run both solvers and compare results
compareApproaches :: [Int] -> Int -> ComparisonResult
compareApproaches elems target =
  let bfSols   = normalize $ map fst (solveBruteForce elems target)
      dpSols   = normalize $ solveDPAll elems target
      pathCnt  = length (allPaths elems)
      classCnt = Map.size (dpTable elems)
  in CR
    { bfSolutions  = bfSols
    , dpSolutions  = dpSols
    , bfPathCount  = pathCnt
    , dpClassCount = classCnt
    , agree        = bfSols == dpSols
    }
  where
    normalize = sort . map sort

showComparison :: ComparisonResult -> String
showComparison cr = unlines
  [ "  Brute Force solutions: " ++ show (bfSolutions cr)
  , "  DP solutions:          " ++ show (dpSolutions cr)
  , "  Agreement:             " ++ show (agree cr)
  , "  BF paths explored:     " ++ show (bfPathCount cr) ++ " (2^n)"
  , "  DP equiv. classes:     " ++ show (dpClassCount cr)
  , "  Compression ratio:     " ++ show (bfPathCount cr) ++ " -> " ++ show (dpClassCount cr)
      ++ " (" ++ show ratio ++ "x)"
  ]
  where
    ratio :: Double
    ratio = fromIntegral (bfPathCount cr) / max 1 (fromIntegral (dpClassCount cr))
