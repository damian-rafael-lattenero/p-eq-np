module PeqNP.MyhillNerode
  ( MNResult(..)
  , mnClassify
  , mnClassesPerLevel
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import PeqNP.DPSolver (dpReachable)

-- | Result of Myhill-Nerode classification at one level of the decision tree.
--
-- Two partial sums s1, s2 are MN-equivalent at level i if:
-- canReachTarget(s1, remaining_i, T) == canReachTarget(s2, remaining_i, T)
--
-- For Subset Sum, this simplifies to:
-- s1 ~ s2 iff (T - s1) is reachable from remaining ↔ (T - s2) is reachable from remaining
--
-- KEY INSIGHT: this gives only 2 classes (YES/NO) per level.
-- But computing which class a sum belongs to IS the NP-hard problem.
data MNResult = MNResult
  { mnN               :: Int
  , mnTarget          :: Int
  , mnClassesPerLvl   :: [Int]   -- distinct MN classes per level
  , mnSumsPerLvl      :: [Int]   -- distinct partial sums per level (for comparison)
  } deriving (Show)

-- | Classify partial sums at each level by Myhill-Nerode equivalence.
--
-- At level i, we've processed elements [e0..e_{i-1}].
-- Remaining elements are [e_i..e_{n-1}].
-- For each reachable partial sum s, compute:
--   canReach(s) = (target - s) ∈ dpReachable(remaining)
-- Two sums are MN-equivalent iff they have the same canReach value.
mnClassify :: [Int] -> Int -> MNResult
mnClassify elems target =
  let n = length elems
      levels = go [] elems (Set.singleton 0)
  in MNResult
    { mnN             = n
    , mnTarget        = target
    , mnClassesPerLvl = map fst levels
    , mnSumsPerLvl    = map snd levels
    }
  where
    go :: [Int] -> [Int] -> Set Int -> [(Int, Int)]
    go _processed [] reachableSums =
      -- At the leaves: each sum is its own class, and MN has 2 classes
      let mnClasses = Set.size $ Set.map (== target) reachableSums
      in [(mnClasses, Set.size reachableSums)]
    go processed (x:remaining) reachableSums =
      let -- How many distinct MN classes at this level?
          -- canReach(s) = (target - s) can be formed from remaining elements
          remainReachable = dpReachable remaining
          classify s = (target - s) `Set.member` remainReachable
          mnClasses = Set.size $ Set.map classify reachableSums
          numSums = Set.size reachableSums
          -- Advance to next level: each sum branches to s (skip) and s+x (include)
          nextSums = Set.union reachableSums (Set.map (+ x) reachableSums)
      in (mnClasses, numSums) : go (processed ++ [x]) remaining nextSums

-- | Just the MN classes per level (convenience)
mnClassesPerLevel :: [Int] -> Int -> [Int]
mnClassesPerLevel elems target = mnClassesPerLvl (mnClassify elems target)
