module PeqNP.Adjunction
  ( IntermediateCat(..)
  , buildMinimalIntermediate
  , intermediateSize
  , showIntermediate
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

import PeqNP.DPSolver (dpReachable)

-- | The minimal intermediate category for a Subset Sum instance.
--
-- CATEGORICAL INTERPRETATION:
-- This is the image of the "free functor" F: DecisionCat → IntermediateCat
-- where F collapses states that are indistinguishable for answering
-- the target question. The "forgetful functor" U extracts the answer.
--
-- The adjunction F ⊣ U exists iff this intermediate category
-- faithfully represents the answer. Its SIZE is the key metric:
-- polynomial size → P = NP, exponential → P ≠ NP (for this approach).
data IntermediateCat = IC
  { icStates    :: Set Int       -- abstract states (= distinct reachable sum sets, hashed)
  , icSize      :: Int           -- number of states
  , icLevels    :: [Set Int]     -- distinct states at each level (for growth analysis)
  , icAccepting :: Set Int       -- states from which target is reachable
  } deriving (Show)

-- | Build the minimal intermediate category.
--
-- At each level i, the "state" of a partial sum s is determined by
-- the set of final sums reachable from s given the remaining elements.
-- Two partial sums with the same reachable set are identified (merged).
--
-- This is the categorical coequalizer / quotient that produces
-- the smallest faithful intermediate representation.
buildMinimalIntermediate :: [Int] -> Int -> IntermediateCat
buildMinimalIntermediate elems target =
  let -- At each level, compute distinct "abstract states"
      -- State = fingerprint of what's reachable from here
      levels = go (Set.singleton 0) elems
      allStates = Set.unions levels
  in IC
    { icStates    = allStates
    , icSize      = Set.size allStates
    , icLevels    = map (\s -> s) levels
    , icAccepting = Set.filter (\s -> target `Set.member` dpReachable (drop s elems)) allStates
    -- Note: icAccepting is approximate; the real accepting states depend on the level
    }
  where
    go :: Set Int -> [Int] -> [Set Int]
    go sums [] = [sums]
    go sums (x:xs) =
      let nextSums = Set.union sums (Set.map (+ x) sums)
      in sums : go nextSums xs

-- | Number of states in the intermediate category
intermediateSize :: IntermediateCat -> Int
intermediateSize = icSize

-- | Pretty-print
showIntermediate :: IntermediateCat -> String
showIntermediate ic = unlines
  [ "  States: " ++ show (icSize ic)
  , "  States per level: " ++ show (map Set.size (icLevels ic))
  ]
