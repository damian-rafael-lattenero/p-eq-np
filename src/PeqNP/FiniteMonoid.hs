module PeqNP.FiniteMonoid
  ( -- * Typeclass
    FiniteMonoid(..)
    -- * ZMod k — integers modulo k
  , ZMod(..)
    -- * Boolean monoids
  , BoolOr(..)
  , BoolAnd(..)
    -- * Product monoid
  , ProductMonoid(..)
  ) where

import Data.Proxy (Proxy(..))
import GHC.TypeNats (Nat, KnownNat, natVal)

-- | A finite monoid: a monoid with a finite, enumerable set of elements.
--
-- This is the target category for our answer-preserving functors.
-- The P=NP question becomes: does there exist a FiniteMonoid M of
-- polynomial size in n such that some homomorphism Z → M preserves
-- the Subset Sum answer?
class (Monoid m, Eq m, Ord m) => FiniteMonoid m where
  -- | All elements of the monoid (must be finite and complete)
  elements :: [m]

-- ═══════════════════════════════════════════════════════════
-- ZMod k — The key finite monoid: integers modulo k
-- ═══════════════════════════════════════════════════════════

-- | Integers modulo k, with modular addition as the monoid operation.
--
-- Unlike the broken `modularFunctor` from Phase C (which used Sum with
-- regular +), ZMod k has <> = modular addition baked into the Semigroup
-- instance. This means composed enriched arrows in EnrichedArrow (ZMod k)
-- correctly accumulate metadata with modular arithmetic.
--
-- The modulus k is encoded at the type level via GHC TypeNats.
newtype ZMod (k :: Nat) = ZMod { getZMod :: Int }
  deriving (Eq, Ord)

instance KnownNat k => Show (ZMod k) where
  show (ZMod v) = show v ++ " mod " ++ show (natVal (Proxy :: Proxy k))

instance KnownNat k => Semigroup (ZMod k) where
  ZMod a <> ZMod b = ZMod ((a + b) `mod` k')
    where k' = fromIntegral (natVal (Proxy :: Proxy k))

instance KnownNat k => Monoid (ZMod k) where
  mempty = ZMod 0

instance KnownNat k => FiniteMonoid (ZMod k) where
  elements = [ZMod i | i <- [0 .. fromIntegral (natVal (Proxy :: Proxy k)) - 1]]

-- ═══════════════════════════════════════════════════════════
-- Boolean monoids
-- ═══════════════════════════════════════════════════════════

-- | (Bool, ||, False) — the "has anything been included?" monoid.
--
-- The unique nontrivial homomorphism h: (Z,+) → BoolOr maps:
--   h(0) = False, h(n) = True for n > 0
-- This is maximally lossy: it only knows whether ANY element was included,
-- not which ones or how many. Cannot solve Subset Sum in general.
newtype BoolOr = BoolOr { getBoolOr :: Bool }
  deriving (Show, Eq, Ord)

instance Semigroup BoolOr where
  BoolOr a <> BoolOr b = BoolOr (a || b)

instance Monoid BoolOr where
  mempty = BoolOr False

instance FiniteMonoid BoolOr where
  elements = [BoolOr False, BoolOr True]

-- | (Bool, &&, True) — the "have all elements been included?" monoid.
newtype BoolAnd = BoolAnd { getBoolAnd :: Bool }
  deriving (Show, Eq, Ord)

instance Semigroup BoolAnd where
  BoolAnd a <> BoolAnd b = BoolAnd (a && b)

instance Monoid BoolAnd where
  mempty = BoolAnd True

instance FiniteMonoid BoolAnd where
  elements = [BoolAnd False, BoolAnd True]

-- ═══════════════════════════════════════════════════════════
-- Product monoid
-- ═══════════════════════════════════════════════════════════

-- | Product of two monoids: componentwise operation.
--
-- By the Chinese Remainder Theorem:
-- ZMod k1 × ZMod k2 ≅ ZMod (k1*k2) when gcd(k1,k2) = 1
--
-- This allows building larger finite monoids from smaller ones.
newtype ProductMonoid m1 m2 = PM { getPM :: (m1, m2) }
  deriving (Eq, Ord)

instance (Show m1, Show m2) => Show (ProductMonoid m1 m2) where
  show (PM (a, b)) = "(" ++ show a ++ ", " ++ show b ++ ")"

instance (Semigroup m1, Semigroup m2) => Semigroup (ProductMonoid m1 m2) where
  PM (a1, a2) <> PM (b1, b2) = PM (a1 <> b1, a2 <> b2)

instance (Monoid m1, Monoid m2) => Monoid (ProductMonoid m1 m2) where
  mempty = PM (mempty, mempty)

instance (FiniteMonoid m1, FiniteMonoid m2) => FiniteMonoid (ProductMonoid m1 m2) where
  elements = [PM (a, b) | a <- elements, b <- elements]
