module PeqNP.Search
  ( SearchResult(..)
  , MonoidReport(..)
  , searchMonoid
  , testGenerator
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import PeqNP.SubsetSum (Sum(..))
import PeqNP.DPSolver (dpTable)
import PeqNP.FiniteMonoid (FiniteMonoid(..))
import PeqNP.Homomorphism (MonoidHom(..), allHomomorphisms)

-- | Result of testing one generator (one homomorphism)
data SearchResult m = SR
  { srGenerator      :: m
  , srPreserves      :: Bool  -- ^ Does this homomorphism preserve the answer?
  , srFalsePositives :: Int   -- ^ Reachable sums ≠ target that collide with target
  , srImageSize      :: Int   -- ^ |image(h)| — distinct values hit in M
  } deriving (Show)

-- | Report for testing ALL homomorphisms from Z to a given monoid
data MonoidReport m = MR
  { mrMonoidName  :: String
  , mrMonoidSize  :: Int
  , mrTarget      :: Int
  , mrHasSolution :: Bool    -- ^ Does the instance actually have a solution?
  , mrResults     :: [SearchResult m]
  , mrAnyPreserve :: Bool    -- ^ Does ANY homomorphism preserve the answer?
  } deriving (Show)

-- | Test all homomorphisms from (Z,+) to M for a given Subset Sum instance.
--
-- Uses dpTable (O(n*T)) instead of allPaths (O(2^n)) to get reachable sums.
--
-- KEY INSIGHT:
-- - If target IS reachable: every homomorphism preserves the answer
--   (a YES is always mapped to a YES).
-- - If target is NOT reachable: preserves iff h(target) ∉ {h(s) | s reachable}
--   (no reachable sum collides with target under h).
searchMonoid
  :: (FiniteMonoid m, Show m)
  => String -> [Int] -> Int -> MonoidReport m
searchMonoid name elems target =
  let table = dpTable elems
      reachableSums = Set.fromList (Map.keys table)
      hasSolution = Set.member target reachableSums
      homs = allHomomorphisms
      results = map (\hom -> testGenerator hom reachableSums target) homs
  in MR
    { mrMonoidName  = name
    , mrMonoidSize  = length homs  -- |M| = number of generators = number of elements
    , mrTarget      = target
    , mrHasSolution = hasSolution
    , mrResults     = results
    , mrAnyPreserve = any srPreserves results
    }

-- | Test a single generator/homomorphism against a set of reachable sums.
testGenerator
  :: (Eq n, Ord n)
  => MonoidHom Sum n -> Set.Set Int -> Int -> SearchResult n
testGenerator hom reachableSums target =
  let h = applyHom hom
      targetImage = h (Sum target)
      hasSolution = Set.member target reachableSums
      -- Map all reachable sums through h
      reachableImages = Set.map (\s -> (s, h (Sum s))) reachableSums
      -- False positives: reachable sums ≠ target that map to same image as target
      collisions = Set.filter (\(s, img) -> img == targetImage && s /= target) reachableImages
      -- Image size: distinct values in M that are hit
      imgSize = Set.size (Set.map snd reachableImages)
      -- Preservation:
      -- YES instance: always preserved
      -- NO instance: preserved iff no collision
      preserves = if hasSolution
                  then True
                  else Set.null collisions
  in SR
    { srGenerator      = targetImage  -- h(target), useful for display
    , srPreserves      = preserves
    , srFalsePositives = Set.size collisions
    , srImageSize      = imgSize
    }
