module PeqNP.Quotient
  ( QuotientHom(..)
  , quotientByMetadata
  , lookupTarget
  , quotientSize
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import PeqNP.EnrichedArrow (EnrichedArrow(..))

-- | A quotiented hom-object: morphisms grouped by metadata equivalence.
--
-- THE CATEGORICAL VIEW OF DP:
-- The full hom-object Hom(a, b) has 2^n morphisms in it.
-- Each morphism has metadata in a monoid M.
-- The quotient Hom(a,b) / ~  where  f ~ g iff metadata f == metadata g
-- collapses this to |M_reachable| equivalence classes.
--
-- This is EXACTLY what dynamic programming does: instead of tracking
-- all paths, it tracks one representative per distinct partial sum.
-- The QuotientHom makes this categorical operation explicit.

data QuotientHom m a b = QHom
  { classes :: Map m (EnrichedArrow m a b)
    -- ^ One representative arrow per distinct metadata value
  }

-- | Quotient a list of morphisms by metadata equivalence.
-- Keeps the first representative encountered for each metadata value.
quotientByMetadata :: Ord m => [EnrichedArrow m a b] -> QuotientHom m a b
quotientByMetadata arrows = QHom
  { classes = Map.fromList [(metadata a, a) | a <- arrows]
  }

-- | Check if a target metadata value is reachable in the quotiented hom.
lookupTarget :: Ord m => m -> QuotientHom m a b -> Maybe (EnrichedArrow m a b)
lookupTarget m (QHom cs) = Map.lookup m cs

-- | Number of equivalence classes (distinct metadata values)
quotientSize :: QuotientHom m a b -> Int
quotientSize (QHom cs) = Map.size cs
