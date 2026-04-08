module PeqNP.Homomorphism
  ( MonoidHom(..)
  , fromGenerator
  , allHomomorphisms
  ) where

import PeqNP.SubsetSum (Sum(..))
import PeqNP.FiniteMonoid (FiniteMonoid(..))

-- | A monoid homomorphism from m to n.
--
-- For our purposes, the source is always (Sum, +, 0) = (Z, +, 0)
-- and the target is a FiniteMonoid.
--
-- KEY FACT: A homomorphism h : (Z, +) → (M, <>) is entirely
-- determined by h(1), since h(n) = h(1)^n = stimes n (h 1).
data MonoidHom m n = MonoidHom
  { homName  :: String
  , applyHom :: m -> n
  }

-- | Construct the unique homomorphism h : (Z,+) → M where h(1) = g.
-- For n >= 0: h(n) = g <> g <> ... <> g  (n times)
-- For n = 0: h(0) = mempty
fromGenerator :: (Monoid m, Show m) => m -> MonoidHom Sum m
fromGenerator g = MonoidHom
  { homName  = "h(1)=" ++ show g
  , applyHom = \(Sum n) -> mtimes (abs n) g
  }

-- | Repeat a monoid element n times: m <> m <> ... <> m
-- mtimes 0 m = mempty, mtimes n m = m <> mtimes (n-1) m
mtimes :: Monoid m => Int -> m -> m
mtimes n m
  | n <= 0    = mempty
  | otherwise = m <> mtimes (n - 1) m

-- | All possible homomorphisms from (Z,+) to a FiniteMonoid M.
-- One per element of M (each element is a candidate for h(1)).
allHomomorphisms :: (FiniteMonoid m, Show m) => [MonoidHom Sum m]
allHomomorphisms = map fromGenerator elements
