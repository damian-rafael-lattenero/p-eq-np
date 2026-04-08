module PeqNP.EnrichedCategory where

-- | An enriched category over a monoidal structure V.
--
-- In a V-enriched category:
--   - Hom-objects are not mere sets, they are objects in V
--   - Composition carries structure: it combines metadata monoically
--   - Identity arrows carry the monoidal unit as metadata
--
-- For our Subset Sum exploration, V = (Z, +, 0):
--   each morphism "knows" how much partial sum it has accumulated.

class Monoid m => EnrichedCategory m cat where
  -- | Identity morphism with neutral metadata
  eid :: cat m a a

  -- | Enriched composition: composes arrows AND combines metadata
  (|.|) :: cat m b c -> cat m a b -> cat m a c
