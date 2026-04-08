module PeqNP.EnrichedArrow where

import PeqNP.EnrichedCategory

-- | An arrow that carries structural metadata alongside its computation.
--
-- Unlike a plain function (a -> b), an EnrichedArrow knows something
-- about the "cost" or "accumulation" of its path through the decision tree.
--
-- This is the key insight: composition is no longer "naked".
-- When you compose two enriched arrows, the metadata combines monoidally,
-- giving you a structurally rich pipeline where each step "remembers"
-- what happened before it — without re-traversing.

data EnrichedArrow m a b = EA
  { metadata :: m        -- ^ Structural information (e.g., partial sum)
  , runArrow :: a -> b   -- ^ The actual computation
  }

instance Monoid m => EnrichedCategory m EnrichedArrow where
  eid = EA mempty id

  (EA m2 f) |.| (EA m1 g) = EA (m1 <> m2) (f . g)

-- | Lift a plain function into an enriched arrow with given metadata
enrich :: m -> (a -> b) -> EnrichedArrow m a b
enrich = EA

-- | Lift a plain function with neutral metadata
liftPure :: Monoid m => (a -> b) -> EnrichedArrow m a b
liftPure = EA mempty
