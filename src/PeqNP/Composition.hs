module PeqNP.Composition where

import PeqNP.EnrichedCategory (EnrichedCategory(eid, (|.|)))
import PeqNP.EnrichedArrow

-- | The enriched composition operator.
--
-- In classical category theory:    (.) :: (b -> c) -> (a -> b) -> (a -> c)
-- In our enriched category:        (⊗) :: EA m b c -> EA m a b -> EA m a c
--
-- The difference: (⊗) also combines the metadata monoidally.
-- This means a composed pipeline carries the FULL structural history
-- of its path, available for inspection WITHOUT re-execution.
--
-- WHY THIS MATTERS FOR SUBSET SUM:
-- Each decision (include element / skip element) is an enriched arrow.
-- "Include x" carries metadata (Sum x).
-- A path through the decision tree is a composition of these arrows.
-- The metadata of the composed path IS the partial sum — computed once,
-- propagated structurally, available for algebraic manipulation.

-- | Infix enriched composition (right-to-left, like (.))
(⊗) :: Monoid m => EnrichedArrow m b c -> EnrichedArrow m a b -> EnrichedArrow m a c
(⊗) = (|.|)

-- | Left-to-right enriched composition (like (>>>))
(⊕) :: Monoid m => EnrichedArrow m a b -> EnrichedArrow m b c -> EnrichedArrow m a c
f ⊕ g = g ⊗ f

-- | Compose a list of enriched arrows (left-to-right)
composeAll :: Monoid m => [EnrichedArrow m a a] -> EnrichedArrow m a a
composeAll = foldl (⊕) eid
