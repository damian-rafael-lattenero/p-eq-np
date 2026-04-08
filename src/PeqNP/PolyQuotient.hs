module PeqNP.PolyQuotient
  ( PolyMod(..)
  , quotientPoly
  , polyModMul
  , polyModOne
  , includeFactorMod
  , polyModHasCoeff
  , polyModCoeffAt
  , buildProductMod
    -- * Search
  , minPreservingQ
  , PolyScalingPoint(..)
  , polyScaling
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.List (find)

import PeqNP.Polynomial (Poly(..), coeffAt, expand, ProductForm(..))
import PeqNP.Impossibility (minDistinguishingModulus, MinSizeResult(..))

-- | Polynomial modulo (x^q - 1).
--
-- In Z[x]/(x^q - 1), x^k ≡ x^(k mod q). Coefficients of same
-- residue class are ADDED together (they "wrap around").
--
-- This quotient ring has at most q distinct "positions" (0..q-1).
-- It's a lossy compression of the full polynomial:
-- - If q ≥ max_degree + 1: lossless (no wraparound)
-- - If q < max_degree + 1: positions collide, potential false positives
--
-- THE QUESTION: can q be polynomial in n while avoiding false positives
-- at position T mod q?
data PolyMod = PM
  { pmCoeffs :: Map Int Int  -- exponent (0..q-1) → summed coefficient
  , pmQ      :: Int          -- the modulus q
  } deriving (Show, Eq)

-- | Reduce a full polynomial modulo (x^q - 1)
quotientPoly :: Int -> Poly -> PolyMod
quotientPoly q (Poly m) = PM
  { pmCoeffs = Map.filter (/= 0) $ Map.fromListWith (+)
      [ (e `mod` q, c) | (e, c) <- Map.toList m ]
  , pmQ = q
  }

-- | Multiplicative identity in the quotient ring
polyModOne :: Int -> PolyMod
polyModOne q = PM (Map.singleton 0 1) q

-- | Multiplication in Z[x]/(x^q - 1)
polyModMul :: PolyMod -> PolyMod -> PolyMod
polyModMul (PM a q1) (PM b _q2) = PM
  { pmCoeffs = Map.filter (/= 0) $ Map.fromListWith (+)
      [ ((ea + eb) `mod` q1, ca * cb)
      | (ea, ca) <- Map.toList a
      , (eb, cb) <- Map.toList b
      ]
  , pmQ = q1
  }

-- | Factor (1 + x^w) in the quotient ring
includeFactorMod :: Int -> Int -> PolyMod
includeFactorMod q w = PM (Map.fromListWith (+) [(0, 1), (w `mod` q, 1)]) q

-- | Build the full product Π(1 + x^wᵢ) directly in the quotient ring.
-- This is O(n * q²) — much better than expanding and then quotienting.
buildProductMod :: Int -> [Int] -> PolyMod
buildProductMod q = foldl (\acc w -> polyModMul acc (includeFactorMod q w)) (polyModOne q)

-- | Get coefficient at position T mod q in the quotient
polyModCoeffAt :: Int -> PolyMod -> Int
polyModCoeffAt t (PM m q) = Map.findWithDefault 0 (t `mod` q) m

-- | Is the coefficient at position T mod q nonzero?
polyModHasCoeff :: Int -> PolyMod -> Bool
polyModHasCoeff t pm = polyModCoeffAt t pm /= 0

-- ═══════════════════════════════════════════════════════════
-- Search: minimum q that preserves the answer
-- ═══════════════════════════════════════════════════════════

-- | Find minimum q such that the quotient preserves the answer.
--
-- For a YES instance (target reachable): any q works (coefficient wraps but stays > 0)
-- For a NO instance: need q where position T mod q has coefficient 0 in the quotient
--
-- COMPARISON WITH ZMod k: ZMod k checks if (target mod k) ∈ {s mod k | s reachable}
-- PolyQuotient checks if [x^(T mod q)] Π(1+x^wᵢ) mod (x^q-1) is nonzero
-- The polynomial quotient can distinguish MORE because it uses the full
-- multiplicative structure, not just additive residues.
minPreservingQ :: [Int] -> Int -> Int -> Maybe Int
minPreservingQ elems target maxQ =
  let fullPoly = expand (PF elems)
      isReachable = coeffAt target fullPoly > 0
  in if isReachable
     then Just 1  -- YES instances: any q works
     else find tryQ [2..maxQ]
  where
    tryQ q =
      let pm = buildProductMod q elems
      in not (polyModHasCoeff target pm)

-- | Scaling data point
data PolyScalingPoint = PSP
  { pspN      :: Int
  , pspTarget :: Int
  , pspMinQ   :: Maybe Int
  , pspMinK   :: Maybe Int  -- for comparison with ZMod k
  } deriving (Show)

-- | Run scaling experiment comparing polynomial quotient vs ZMod k
polyScaling :: [([Int], Int)] -> Int -> [PolyScalingPoint]
polyScaling instances maxBound' =
  [ PSP
    { pspN      = length elems
    , pspTarget = target
    , pspMinQ   = minPreservingQ elems target maxBound'
    , pspMinK   = minPreservingK elems target maxBound'
    }
  | (elems, target) <- instances
  ]
  where
    minPreservingK elems target maxK =
      msrMinModulus (minDistinguishingModulus elems target maxK)
