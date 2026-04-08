module PeqNP.Polynomial
  ( -- * Polynomial type
    Poly(..)
  , polyOne
  , polyZero
  , polyFromList
  , polyMul
  , coeffAt
  , hasCoeff
  , degree
  , nonzeroTerms
    -- * Product form
  , ProductForm(..)
  , expand
  , includeFactor
    -- * Display
  , showPoly
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.List (intercalate)

-- | Sparse polynomial over Z, represented as Map from exponent to coefficient.
--
-- In our framework, this is the enrichment monoid (Z[x], *, 1):
-- - "include w" carries metadata (1 + x^w)
-- - "skip w" carries metadata 1
-- - Composition = polynomial multiplication
--
-- The generating function g(x) = Π(1 + x^wᵢ) encodes ALL 2^n subset sums.
-- Coefficient of x^T > 0  iff  some subset sums to T.
newtype Poly = Poly { coeffs :: Map Int Int }
  deriving (Eq, Ord)

instance Show Poly where
  show = showPoly

-- | Multiplicative identity: 1
polyOne :: Poly
polyOne = Poly (Map.singleton 0 1)

-- | Zero polynomial
polyZero :: Poly
polyZero = Poly Map.empty

-- | Build from list of (exponent, coefficient) pairs
polyFromList :: [(Int, Int)] -> Poly
polyFromList = Poly . Map.filter (/= 0) . Map.fromListWith (+)

-- | Polynomial multiplication (convolution)
polyMul :: Poly -> Poly -> Poly
polyMul (Poly a) (Poly b) = Poly $ Map.filter (/= 0) $
  Map.fromListWith (+)
    [ (ea + eb, ca * cb)
    | (ea, ca) <- Map.toList a
    , (eb, cb) <- Map.toList b
    ]

-- | Monoid under multiplication
instance Semigroup Poly where
  (<>) = polyMul

instance Monoid Poly where
  mempty = polyOne

-- | Get coefficient of x^k
coeffAt :: Int -> Poly -> Int
coeffAt k (Poly m) = Map.findWithDefault 0 k m

-- | Is the coefficient of x^k nonzero?
hasCoeff :: Int -> Poly -> Bool
hasCoeff k p = coeffAt k p /= 0

-- | Degree of the polynomial (-1 for zero poly)
degree :: Poly -> Int
degree (Poly m)
  | Map.null m = -1
  | otherwise  = fst (Map.findMax m)

-- | Number of nonzero terms
nonzeroTerms :: Poly -> Int
nonzeroTerms (Poly m) = Map.size m

-- ═══════════════════════════════════════════════════════════
-- Product form: O(n) representation
-- ═══════════════════════════════════════════════════════════

-- | Product form: g(x) = Π(1 + x^wᵢ)
-- O(n) representation that encodes 2^n subset sums.
newtype ProductForm = PF { pfFactors :: [Int] }
  deriving (Show, Eq)

-- | Expand product form to sparse polynomial (up to O(2^n) terms)
expand :: ProductForm -> Poly
expand (PF factors) = foldl (\acc w -> acc <> includeFactor w) polyOne factors

-- | Single factor (1 + x^w)
includeFactor :: Int -> Poly
includeFactor w = polyFromList [(0, 1), (w, 1)]

-- ═══════════════════════════════════════════════════════════
-- Display
-- ═══════════════════════════════════════════════════════════

showPoly :: Poly -> String
showPoly (Poly m)
  | Map.null m = "0"
  | otherwise  = intercalate " + " $ map showTerm (Map.toAscList m)
  where
    showTerm (0, c) = show c
    showTerm (1, 1) = "x"
    showTerm (1, c) = show c ++ "x"
    showTerm (e, 1) = "x^" ++ show e
    showTerm (e, c) = show c ++ "x^" ++ show e
