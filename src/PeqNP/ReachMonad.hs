module PeqNP.ReachMonad
  ( -- * Reachability tree
    ReachTree(..)
  , buildReachTree
    -- * Analysis
  , distinctStatesPerLevel
  , totalDistinctStates
  , treeDepth
  , showReachTree
  , reachSetOf
  ) where

import qualified Data.Set as Set
import Data.Set (Set)


-- | A decision tree annotated with FORWARD reachability sets.
--
-- Instead of tracking "what sum have I accumulated so far?" (backward, = Sum),
-- we track "what final sums can I still reach from here?" (forward, = Set Int).
--
-- This is the categorical "join" of the reachability monad:
-- at each node, we know the FULL set of possible outcomes from this point.
--
-- THE KEY QUESTION: how many DISTINCT ReachSets appear across the tree?
-- If polynomial in n → there exists a polynomial intermediate structure.
-- If exponential → the reachability monad doesn't help compress.
data ReachTree
  = Leaf (Set Int)                        -- terminal: reachable sums = {accumulated sum}
  | Branch Int (Set Int) ReachTree ReachTree
    -- element, reachable sums from this node, include branch, skip branch
  deriving (Show, Eq)

-- | Build the reachability-annotated decision tree.
--
-- At each node, the ReachSet is the union of the ReachSets of its children,
-- adjusted for the decision (include adds the element, skip doesn't).
--
-- This is O(2^n) in the tree itself, but we're measuring the number
-- of DISTINCT sets, not the tree size.
buildReachTree :: [Int] -> ReachTree
buildReachTree = go 0
  where
    go acc [] = Leaf (Set.singleton acc)
    go acc (x:xs) =
      let includeTree = go (acc + x) xs
          skipTree    = go acc xs
          reachable   = reachSetOf includeTree `Set.union` reachSetOf skipTree
      in Branch x reachable includeTree skipTree

-- | Extract the reachability set from a tree node
reachSetOf :: ReachTree -> Set Int
reachSetOf (Leaf s)           = s
reachSetOf (Branch _ s _ _)   = s

-- | Count distinct reachability sets at each level of the tree.
--
-- Level 0 = root (1 set), level n = leaves (up to 2^n sets).
-- The profile of distinct sets per level reveals how quickly
-- the intermediate structure grows.
distinctStatesPerLevel :: ReachTree -> [Int]
distinctStatesPerLevel tree = map Set.size (go tree)
  where
    go :: ReachTree -> [Set (Set Int)]
    go (Leaf s) = [Set.singleton s]
    go (Branch _ s l r) =
      let lLevels = go l
          rLevels = go r
          merged = zipWithDefault Set.empty Set.union lLevels rLevels
      in Set.singleton s : merged

    zipWithDefault :: a -> (a -> a -> a) -> [a] -> [a] -> [a]
    zipWithDefault _   _ []     []     = []
    zipWithDefault def f []     (y:ys) = f def y : zipWithDefault def f [] ys
    zipWithDefault def f (x:xs) []     = f x def : zipWithDefault def f xs []
    zipWithDefault def f (x:xs) (y:ys) = f x y   : zipWithDefault def f xs ys

-- | Total number of distinct reachability sets across all levels.
-- This is the "size of the reachability monad's state space."
totalDistinctStates :: ReachTree -> Int
totalDistinctStates = sum . distinctStatesPerLevel

-- | Depth of the tree (= number of elements)
treeDepth :: ReachTree -> Int
treeDepth (Leaf _)         = 0
treeDepth (Branch _ _ l _) = 1 + treeDepth l

-- | Pretty-print summary of a reachability tree
showReachTree :: ReachTree -> String
showReachTree tree = unlines $
  [ "  Depth (n): " ++ show (treeDepth tree)
  , "  Root reachability: " ++ show (Set.size (reachSetOf tree)) ++ " distinct sums"
  , "  Distinct states per level: " ++ show (distinctStatesPerLevel tree)
  , "  Total distinct states: " ++ show (totalDistinctStates tree)
  ]
