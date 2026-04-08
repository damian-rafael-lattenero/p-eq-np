{-# LANGUAGE RankNTypes #-}

module PeqNP.Functor
  ( EnrichedFunctor(..)
  , applyFunctor
  , fromHomomorphism
  -- * Concrete functors
  , modularFunctor
  , modularFunctorZMod
  , withModulus
  , forgetfulFunctor
  , identityFunctor
  ) where

import Data.Proxy (Proxy(..))
import GHC.TypeNats (KnownNat, SomeNat(..), natVal, someNatVal)
import Numeric.Natural (Natural)

import PeqNP.EnrichedArrow (EnrichedArrow(..))
import PeqNP.SubsetSum (Sum(..))
import PeqNP.FiniteMonoid (ZMod(..))
import PeqNP.Homomorphism (MonoidHom(..))

-- | A functor between enriched categories that changes the enrichment monoid.
--
-- THE P=NP QUESTION in this framework:
-- Does there exist an EnrichedFunctor F : (EnrichedArrow Sum) → (EnrichedArrow M)
-- where M is a FINITE monoid of polynomial size in n, such that
-- F preserves the answer to "does any path reach target T"?
data EnrichedFunctor m n = EF
  { functorName :: String
  , mapMeta     :: m -> n
  , mapArrow    :: forall a b. EnrichedArrow m a b -> EnrichedArrow n a b
  }

-- | Apply a functor to a list of arrows
applyFunctor :: EnrichedFunctor m n -> [EnrichedArrow m a b] -> [EnrichedArrow n a b]
applyFunctor ef = map (mapArrow ef)

-- | Lift a MonoidHom into an EnrichedFunctor
fromHomomorphism :: MonoidHom m n -> EnrichedFunctor m n
fromHomomorphism hom = EF
  { functorName = homName hom
  , mapMeta     = applyHom hom
  , mapArrow    = \(EA m f) -> EA (applyHom hom m) f
  }

-- ═══════════════════════════════════════════════════════════
-- Concrete functors
-- ═══════════════════════════════════════════════════════════

-- | Legacy modular functor mapping Sum → Sum (for backward compat).
-- NOTE: This is NOT a true enriched functor because Sum's <> is plain +,
-- not modular addition. Use modularFunctorZMod for the correct version.
modularFunctor :: Int -> EnrichedFunctor Sum Sum
modularFunctor k = EF
  { functorName = "mod " ++ show k
  , mapMeta     = \(Sum n) -> Sum (n `mod` k)
  , mapArrow    = \(EA (Sum n) f) -> EA (Sum (n `mod` k)) f
  }

-- | Correct modular functor: Sum → ZMod k with proper modular arithmetic.
--
-- This IS a true enriched functor because ZMod k's <> is modular addition:
-- mapMeta (Sum a <> Sum b) = ZMod ((a+b) mod k)
-- mapMeta (Sum a) <> mapMeta (Sum b) = ZMod (a mod k) <> ZMod (b mod k)
--                                    = ZMod ((a mod k + b mod k) mod k)
--                                    = ZMod ((a+b) mod k)  ✓
modularFunctorZMod :: forall k. KnownNat k => EnrichedFunctor Sum (ZMod k)
modularFunctorZMod =
  let k' = fromIntegral (natVal (Proxy :: Proxy k))
  in EF
    { functorName = "mod " ++ show k'
    , mapMeta     = \(Sum n) -> ZMod (n `mod` k')
    , mapArrow    = \(EA (Sum n) f) -> EA (ZMod (n `mod` k')) f
    }

-- | Use a runtime Int as modulus, dispatching to the type-level version.
-- This bridges runtime values and type-level naturals via someNatVal.
withModulus :: Int -> (forall k. KnownNat k => EnrichedFunctor Sum (ZMod k) -> r) -> r
withModulus k f =
  case someNatVal (fromIntegral k :: Natural) of
    SomeNat (_ :: Proxy k) -> f (modularFunctorZMod @k)

-- | The forgetful functor: strips all metadata.
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
