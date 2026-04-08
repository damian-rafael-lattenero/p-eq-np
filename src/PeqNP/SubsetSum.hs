module PeqNP.SubsetSum where

import PeqNP.EnrichedArrow

-- | For Subset Sum, our metadata monoid is (Sum Int) — additive integers.
--
-- Each decision in the tree is an EnrichedArrow (Sum Int) State State
-- where the metadata tracks the running partial sum.

newtype Sum = Sum { getSum :: Int }
  deriving (Show, Eq, Ord)

instance Semigroup Sum where
  Sum a <> Sum b = Sum (a + b)

instance Monoid Sum where
  mempty = Sum 0

-- | The state carried through the decision tree
data DecisionState = DS
  { remaining :: [Int]   -- ^ Elements not yet decided
  , included  :: [Int]   -- ^ Elements included so far
  } deriving (Show)

-- | Decision: include the next element
include :: Int -> EnrichedArrow Sum DecisionState DecisionState
include x = enrich (Sum x) $ \ds -> ds
  { remaining = drop 1 (remaining ds)
  , included  = x : included ds
  }

-- | Decision: skip the next element
skip :: Int -> EnrichedArrow Sum DecisionState DecisionState
skip _x = enrich (Sum 0) $ \ds -> ds
  { remaining = drop 1 (remaining ds)
  }

-- | Check if an enriched path has reached the target sum
reachedTarget :: Int -> EnrichedArrow Sum a b -> Bool
reachedTarget target ea = getSum (metadata ea) == target

-- | PLACEHOLDER: This is where the radical algebraic transformation goes.
--
-- The question is: can we define a functor F from our enriched category
-- (where objects are decision states and morphisms carry partial sums)
-- to a "simpler" category where the answer is computable in polynomial time?
--
-- Ideas to explore:
--   1. Kan extension that "summarizes" all paths with the same metadata
--   2. Adjunction between the enriched decision category and a polynomial one
--   3. Yoneda: represent each object by its enriched hom-functor,
--      check if the functor has polynomial structure
--   4. Free/forgetful adjunction: what if the free enriched category
--      over the decision graph has a polynomial-time left adjoint?
--
-- For now, this module provides the building blocks.
-- The radical part is in the ideas/ folder and will evolve.
