module PeqNP.PolyEnriched
  ( polyInclude
  , polySkip
  , polyReachedTarget
  , polyAllPaths
  ) where

import PeqNP.EnrichedCategory (EnrichedCategory(eid))
import PeqNP.EnrichedArrow (EnrichedArrow(..), enrich)
import PeqNP.Composition ((⊕))
import PeqNP.SubsetSum (DecisionState(..))
import PeqNP.Polynomial (Poly, includeFactor, polyOne, hasCoeff)

-- | Enriched category over (Z[x], *, 1) instead of (Z, +, 0).
--
-- THE KEY SHIFT:
-- In EnrichedArrow Sum: metadata = partial sum (one integer)
-- In EnrichedArrow Poly: metadata = generating function (a polynomial)
--
-- "include w" carries metadata (1 + x^w) — the polynomial factor
-- "skip w" carries metadata 1 — the multiplicative identity
--
-- After composing all decisions, the metadata is:
--   g(x) = Π (factor_i)
-- where factor_i = (1 + x^wᵢ) if included, 1 if skipped.
--
-- But when we compose ALL paths (both branches), the full product is:
--   G(x) = Π (1 + x^wᵢ) for ALL elements
-- and [x^T] G(x) > 0 iff target T is reachable.

-- | Include element w: metadata = (1 + x^w)
polyInclude :: Int -> EnrichedArrow Poly DecisionState DecisionState
polyInclude w = enrich (includeFactor w) $ \ds -> ds
  { remaining = drop 1 (remaining ds)
  , included  = w : included ds
  }

-- | Skip element: metadata = 1 (multiplicative identity)
polySkip :: Int -> EnrichedArrow Poly DecisionState DecisionState
polySkip _w = enrich polyOne $ \ds -> ds
  { remaining = drop 1 (remaining ds)
  }

-- | Check if target T is reachable: is [x^T] in the metadata polynomial > 0?
polyReachedTarget :: Int -> EnrichedArrow Poly a b -> Bool
polyReachedTarget target ea = hasCoeff target (metadata ea)

-- | Generate all 2^n paths with polynomial metadata
polyAllPaths :: [Int] -> [EnrichedArrow Poly DecisionState DecisionState]
polyAllPaths [] = [eid]
polyAllPaths (x:xs) =
  [ polyInclude x ⊕ arrow | arrow <- subPaths ] ++
  [ polySkip x ⊕ arrow    | arrow <- subPaths ]
  where
    subPaths = polyAllPaths xs
