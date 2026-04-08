module PeqNP.VariableOrdering
  ( OrderingResult(..)
  , processInOrder
  , naturalOrder
  , sortedAsc
  , sortedDesc
  , greedyMinStates
  , allOrderingsExhaustive
  , bestOrdering
  , showOrderingResult
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import Data.List (sortBy, permutations, minimumBy)
import Data.Ord (comparing, Down(..))

-- | Result of processing elements in a specific order
data OrderingResult = OR
  { orOrder          :: [Int]   -- the permutation used
  , orStatesPerLevel :: [Int]   -- distinct partial sums at each level
  , orMaxStates      :: Int     -- maximum across all levels
  , orTotalStates    :: Int     -- sum across all levels
  } deriving (Show)

-- | Process elements in a given order and track distinct partial sums per level.
--
-- This is the BDD-like approach: the ORDER in which we process elements
-- determines how many "states" (distinct partial sums) exist at each level.
-- Different orderings can give dramatically different state counts.
processInOrder :: [Int] -> OrderingResult
processInOrder order =
  let levels = scanl step (Set.singleton 0) order
      stateCounts = map Set.size levels
  in OR
    { orOrder          = order
    , orStatesPerLevel = stateCounts
    , orMaxStates      = maximum stateCounts
    , orTotalStates    = sum stateCounts
    }
  where
    step :: Set Int -> Int -> Set Int
    step sums x = Set.union sums (Set.map (+ x) sums)

-- | Ordering strategies
naturalOrder :: [Int] -> OrderingResult
naturalOrder = processInOrder

sortedAsc :: [Int] -> OrderingResult
sortedAsc = processInOrder . sortBy compare

sortedDesc :: [Int] -> OrderingResult
sortedDesc = processInOrder . sortBy (comparing Down)

-- | Greedy: at each step, pick the element that minimizes the number
-- of distinct states at the NEXT level.
greedyMinStates :: [Int] -> OrderingResult
greedyMinStates elems = processInOrder (go elems (Set.singleton 0))
  where
    go [] _sums = []
    go remaining sums =
      let scored = [ (x, Set.size (Set.union sums (Set.map (+ x) sums)))
                   | x <- remaining ]
          best = fst $ minimumBy (comparing snd) scored
          rest = removeFirst best remaining
      in best : go rest (Set.union sums (Set.map (+ best) sums))

    removeFirst _ [] = []
    removeFirst y (x:xs) = if x == y then xs else x : removeFirst y xs

-- | Exhaustive search: try ALL n! orderings (only for small n!)
allOrderingsExhaustive :: [Int] -> [OrderingResult]
allOrderingsExhaustive = map processInOrder . permutations

-- | Find the ordering with minimum maxStates (exhaustive, small n only)
bestOrdering :: [Int] -> OrderingResult
bestOrdering elems =
  minimumBy (comparing orMaxStates) (allOrderingsExhaustive elems)

-- | Pretty-print
showOrderingResult :: OrderingResult -> String
showOrderingResult or' =
  "  order=" ++ show (orOrder or')
  ++ " states/level=" ++ show (orStatesPerLevel or')
  ++ " max=" ++ show (orMaxStates or')
