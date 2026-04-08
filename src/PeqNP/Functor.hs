{-# LANGUAGE RankNTypes #-}

module PeqNP.Functor
  ( EnrichedFunctor(..)
  , applyFunctor
  , modularFunctor
  , forgetfulFunctor
  , identityFunctor
  ) where

import PeqNP.EnrichedArrow (EnrichedArrow(..))
import PeqNP.SubsetSum (Sum(..))

-- | A functor between enriched categories that changes the enrichment monoid.
--
-- An EnrichedFunctor from (EnrichedArrow m) to (EnrichedArrow n):
--   - Maps metadata via a monoid homomorphism: mapMeta (a <> b) == mapMeta a <> mapMeta b
--   - Preserves the underlying computation (domain/codomain types unchanged)
--
-- THE P=NP QUESTION in this framework:
-- Does there exist an EnrichedFunctor F : (EnrichedArrow Sum) → (EnrichedArrow M)
-- where M is a FINITE monoid of polynomial size in n, such that
-- F preserves the answer to "does any path reach target T"?
--
-- If yes: we've compressed the exponential hom-object to polynomial size.
-- If no for ALL such F: this gives evidence for P ≠ NP.

data EnrichedFunctor m n = EF
  { functorName :: String
  , mapMeta     :: m -> n
    -- ^ The underlying monoid homomorphism on metadata
  , mapArrow    :: forall a b. EnrichedArrow m a b -> EnrichedArrow n a b
    -- ^ The full functor action on arrows
  }

-- | Apply a functor to a list of arrows
applyFunctor :: EnrichedFunctor m n -> [EnrichedArrow m a b] -> [EnrichedArrow n a b]
applyFunctor ef = map (mapArrow ef)

-- | The modular functor: (Z, +, 0) → (Z/kZ, +, 0)
--
-- Maps Sum n → Sum (n mod k). This is a monoid homomorphism because
-- (a + b) mod k ≡ (a mod k + b mod k) mod k.
--
-- This is the "hash-based compression" from open question #1:
-- it collapses the infinite monoid Z to a finite one Z/kZ,
-- producing at most k equivalence classes.
--
-- TRADE-OFF: information is lost. Two paths with different sums
-- may map to the same class. The question is whether we can
-- choose k (or a more sophisticated monoid) to preserve the answer.
modularFunctor :: Int -> EnrichedFunctor Sum Sum
modularFunctor k = EF
  { functorName = "mod " ++ show k
  , mapMeta     = \(Sum n) -> Sum (n `mod` k)
  , mapArrow    = \(EA (Sum n) f) -> EA (Sum (n `mod` k)) f
  }

-- | The forgetful functor: strips all metadata.
--
-- This is the U in the Free ⊣ Forgetful adjunction.
-- Maps everything to the trivial monoid ().
-- ALL information is lost — this is the "maximally lossy" functor.
forgetfulFunctor :: EnrichedFunctor Sum ()
forgetfulFunctor = EF
  { functorName = "forgetful"
  , mapMeta     = const ()
  , mapArrow    = \(EA _ f) -> EA () f
  }

-- | The identity functor: preserves everything.
identityFunctor :: EnrichedFunctor Sum Sum
identityFunctor = EF
  { functorName = "identity"
  , mapMeta     = id
  , mapArrow    = id
  }
