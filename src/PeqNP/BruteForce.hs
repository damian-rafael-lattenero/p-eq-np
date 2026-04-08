module PeqNP.BruteForce
  ( Decision(..)
  , Path
  , allPaths
  , solveBruteForce
  , extractIncluded
  ) where

import PeqNP.EnrichedCategory (EnrichedCategory(eid))
import PeqNP.EnrichedArrow (EnrichedArrow(..))
import PeqNP.Composition ((⊕))
import PeqNP.SubsetSum (Sum(..), DecisionState(..), include, skip, reachedTarget)

-- | A single decision in the Subset Sum tree
data Decision = Include Int | Skip Int
  deriving (Show, Eq)

-- | A complete path through the decision tree
type Path = [Decision]

-- | Generate ALL 2^n decision paths as composed enriched morphisms.
--
-- Each path is a pair of:
--   1. The human-readable decision list
--   2. The composed enriched arrow carrying the accumulated metadata
--
-- The metadata of each composed arrow IS the partial sum of that path,
-- computed structurally via monoidal composition — not by executing the arrow.
allPaths :: [Int] -> [(Path, EnrichedArrow Sum DecisionState DecisionState)]
allPaths [] = [([], eid)]
allPaths (x:xs) =
  [ (Include x : rest, include x ⊕ arrow)
  | (rest, arrow) <- subPaths
  ] ++
  [ (Skip x : rest, skip x ⊕ arrow)
  | (rest, arrow) <- subPaths
  ]
  where
    subPaths = allPaths xs

-- | Solve Subset Sum by brute force: enumerate all 2^n paths,
-- filter by metadata (NOT by executing the arrows).
--
-- Returns pairs of (included elements, enriched arrow).
-- The key demonstration: reachedTarget inspects ONLY the metadata,
-- which was accumulated during composition, not during execution.
solveBruteForce :: [Int] -> Int -> [([Int], EnrichedArrow Sum DecisionState DecisionState)]
solveBruteForce elems target =
  [ (extractIncluded path, arrow)
  | (path, arrow) <- allPaths elems
  , reachedTarget target arrow
  ]

-- | Extract included elements from a decision path
extractIncluded :: Path -> [Int]
extractIncluded [] = []
extractIncluded (Include x : rest) = x : extractIncluded rest
extractIncluded (Skip _ : rest) = extractIncluded rest
