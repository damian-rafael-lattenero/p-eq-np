module PeqNP.DPSolver
  ( dpTable
  , solveDP
  , solveDPAll
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

-- | Dynamic Programming for Subset Sum, framed as categorical quotienting.
--
-- THE CATEGORICAL INSIGHT:
-- Brute force explores the full hom-object: 2^n morphisms in Hom(start, end).
-- Each morphism carries metadata in (Sum Int).
-- DP quotients this hom-object by metadata equivalence:
--   f ~ g  iff  metadata f == metadata g
--
-- The quotiented hom-object has at most O(n * max_sum) equivalence classes,
-- each represented by one path. This is pseudo-polynomial — but categorically,
-- it's a quotient functor collapsing the decision category.

-- | Build the DP table: a map from reachable sums to all subsets achieving them.
--
-- This IS the quotiented hom-object: keys are equivalence classes (partial sums),
-- values are the representative morphisms (subsets).
dpTable :: [Int] -> Map Int [[Int]]
dpTable = foldl step (Map.singleton 0 [[]])
  where
    step table x =
      Map.unionWith (++) table $
        Map.mapKeys (+ x) $
          Map.map (map (x :)) table

-- | Solve: is there any path whose metadata equals the target?
solveDP :: [Int] -> Int -> Maybe [Int]
solveDP elems target =
  case Map.lookup target (dpTable elems) of
    Just (sol:_) -> Just sol
    _            -> Nothing

-- | All solutions (for comparison with brute force)
solveDPAll :: [Int] -> Int -> [[Int]]
solveDPAll elems target =
  case Map.lookup target (dpTable elems) of
    Just sols -> sols
    Nothing   -> []
