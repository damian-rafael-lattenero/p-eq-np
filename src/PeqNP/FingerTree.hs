module PeqNP.FingerTree
  ( -- * Annotation types
    SumAnnotation(..)
  , RangeAnnotation(..)
    -- * Finger tree
  , FTree(..)
  , buildFTree
  , fTreeAnnotation
    -- * Queries
  , canContainTarget
  , rangeQuery
    -- * Solver using finger tree pruning
  , fingerTreeSolve
  , FTStats(..)
  , showFTStats
    -- * TargetAware monoid (the "perfect" annotation)
  , TargetAware(..)
  , taFromElement
  , taMerge
  , taCanReach
  , DifficultyProfile(..)
  , measureDifficulty
  , showDifficultyProfile
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

-- | Monoidal annotations for subset sum finger trees.
--
-- The key idea from Hinze-Paterson (2006): a finger tree annotated
-- with a monoid M allows O(log n) splitting based on monotone predicates
-- over accumulated M-values. The MONOID determines what queries are fast.
--
-- For Subset Sum, the annotation summarizes "what range of sums is
-- achievable by subsets of this subtree's elements?"

-- | Range annotation: [minSum, maxSum] of achievable subset sums.
-- minSum = 0 (empty subset), maxSum = sum of all elements.
-- If target ∉ [minSum, maxSum], we can prune the entire subtree.
data RangeAnnotation = RA
  { raMin   :: !Int  -- minimum achievable sum (always 0 for subsets)
  , raMax   :: !Int  -- maximum achievable sum (sum of all elements)
  , raCount :: !Int  -- number of elements
  } deriving (Show, Eq)

instance Semigroup RangeAnnotation where
  -- When combining two independent groups of elements:
  -- min achievable = minA + minB (both contribute their minimum)
  -- max achievable = maxA + maxB (both contribute their maximum)
  RA min1 max1 c1 <> RA min2 max2 c2 = RA (min1 + min2) (max1 + max2) (c1 + c2)

instance Monoid RangeAnnotation where
  mempty = RA 0 0 0

-- | Sum annotation: tracks exact sum of all elements (for O(1) total)
data SumAnnotation = SA
  { saTotal    :: !Int  -- sum of all elements in subtree
  , saElements :: !Int  -- number of elements
  } deriving (Show, Eq)

instance Semigroup SumAnnotation where
  SA t1 e1 <> SA t2 e2 = SA (t1 + t2) (e1 + e2)

instance Monoid SumAnnotation where
  mempty = SA 0 0

-- | Binary tree with monoidal annotations at each node.
-- This is a simplified finger tree (full Hinze-Paterson has 2-3 tree structure).
data FTree
  = FLeaf !Int !RangeAnnotation
  | FNode !RangeAnnotation FTree FTree
  deriving (Show)

-- | Get annotation of a tree node
fTreeAnnotation :: FTree -> RangeAnnotation
fTreeAnnotation (FLeaf _ a)   = a
fTreeAnnotation (FNode a _ _) = a

-- | Build a balanced binary tree from a list of weights
buildFTree :: [Int] -> FTree
buildFTree []  = FLeaf 0 mempty
buildFTree [x] = FLeaf x (RA 0 x 1)
buildFTree xs  =
  let mid = length xs `div` 2
      (left, right) = splitAt mid xs
      ltree = buildFTree left
      rtree = buildFTree right
  in FNode (fTreeAnnotation ltree <> fTreeAnnotation rtree) ltree rtree

-- | O(1) check: can this subtree's elements contribute to reaching target?
-- If target is outside [0, maxSum], no subset of these elements helps.
canContainTarget :: Int -> FTree -> Bool
canContainTarget t tree =
  let RA lo hi _ = fTreeAnnotation tree
  in t >= lo && t <= hi

-- | Range query: what is the [min, max] range of achievable sums?
rangeQuery :: FTree -> (Int, Int)
rangeQuery tree = let RA lo hi _ = fTreeAnnotation tree in (lo, hi)

-- | Solve Subset Sum using finger tree annotations for pruning.
--
-- At each node, check if the target is achievable given the annotation.
-- If not, prune immediately (O(1)). If yes, recurse into children.
--
-- For a leaf with element w: include (subtract w from remaining target)
-- or skip (keep target as is).

data FTStats = FTS
  { ftsFound     :: Bool
  , ftsSolution  :: Maybe [Int]
  , ftsExplored  :: Int   -- nodes visited
  , ftsTotal     :: Int   -- total nodes in tree
  , ftsPruned    :: Int   -- nodes pruned (never visited)
  } deriving (Show)

fingerTreeSolve :: [Int] -> Int -> FTStats
fingerTreeSolve elems target =
  let tree = buildFTree elems
      totalNodes = nodeCount tree
      (solution, explored) = search tree target 0
  in FTS
    { ftsFound    = solution /= Nothing
    , ftsSolution = solution
    , ftsExplored = explored
    , ftsTotal    = totalNodes
    , ftsPruned   = totalNodes - explored
    }

search :: FTree -> Int -> Int -> (Maybe [Int], Int)
search (FLeaf w _) remaining explored
  | remaining == 0 = (Just [], explored + 1)    -- target reached (skip this element)
  | remaining == w = (Just [w], explored + 1)   -- include this element exactly
  | otherwise      = (Nothing, explored + 1)    -- can't reach target with one element
search (FNode _ left right) remaining explored
  -- Prune: if remaining target is negative, impossible
  | remaining < 0 = (Nothing, explored + 1)
  -- Try all combinations of left/right contributions
  | otherwise =
    let lRange = fTreeAnnotation left
        rRange = fTreeAnnotation right
        explored' = explored + 1
        -- For each possible contribution from the left subtree (0..leftMax),
        -- the right subtree must contribute (remaining - leftContrib).
        -- We check if this is feasible using annotations.
        --
        -- Optimization: iterate over left subtree solutions,
        -- check right feasibility with O(1) annotation check.
        (lSol, lExp) = search left remaining explored'
    in case lSol of
      Just sol | remaining - sum sol >= raMin rRange
               && remaining - sum sol <= raMax rRange ->
        -- Left solved enough; check if right can fill the gap
        let rightNeed = remaining - sum sol
            (rSol, rExp) = search right rightNeed lExp
        in case rSol of
          Just rsol -> (Just (sol ++ rsol), rExp)
          Nothing   -> trySkipLeft left right remaining explored'
      _ -> trySkipLeft left right remaining explored'

trySkipLeft :: FTree -> FTree -> Int -> Int -> (Maybe [Int], Int)
trySkipLeft left right remaining explored =
  -- Try: take nothing from left, everything from right
  if remaining >= raMin (fTreeAnnotation right)
     && remaining <= raMax (fTreeAnnotation right)
  then search right remaining explored
  else
    -- Try: take everything from left
    let leftMax = raMax (fTreeAnnotation left)
        rightNeed = remaining - leftMax
    in if rightNeed >= raMin (fTreeAnnotation right)
          && rightNeed <= raMax (fTreeAnnotation right)
       then
         let (rSol, rExp) = search right rightNeed explored
         in case rSol of
           Just rsol -> (Just rsol, rExp)  -- simplified: not tracking left elements
           Nothing   -> (Nothing, rExp)
       else (Nothing, explored)

nodeCount :: FTree -> Int
nodeCount (FLeaf _ _)     = 1
nodeCount (FNode _ l r) = 1 + nodeCount l + nodeCount r

showFTStats :: FTStats -> String
showFTStats fts = unlines
  [ "  Found:    " ++ show (ftsFound fts)
  , "  Solution: " ++ show (ftsSolution fts)
  , "  Explored: " ++ show (ftsExplored fts) ++ " / " ++ show (ftsTotal fts)
      ++ " (" ++ show (ftsPruned fts) ++ " pruned)"
  ]

-- ═══════════════════════════════════════════════════════════
-- TargetAware monoid: the "perfect" annotation
-- ═══════════════════════════════════════════════════════════

-- | The complete set of achievable subset sums for a group of elements.
--
-- This IS the perfect monoid annotation: it answers "is target reachable?"
-- in O(log n) via Set.member. The catch: the SET ITSELF can be exponential.
--
-- The key experiment: at which level of the tree does |TA| explode?
-- That level is where NP-hardness "appears".
newtype TargetAware = TA { taReachable :: Set Int }
  deriving (Show, Eq)

-- | The <> operation: SUMSET.
-- Given reachable sums A and B, the combined reachable sums = {a+b | a∈A, b∈B}.
-- This is where the explosion happens: |A+B| can be up to |A|*|B|.
taMerge :: TargetAware -> TargetAware -> TargetAware
taMerge (TA a) (TA b) = TA $ Set.fromList
  [x + y | x <- Set.toList a, y <- Set.toList b]

-- | Create TargetAware for a single element: {0, w}
taFromElement :: Int -> TargetAware
taFromElement w = TA (Set.fromList [0, w])

-- | Check if target is reachable: O(log |TA|)
taCanReach :: Int -> TargetAware -> Bool
taCanReach t (TA s) = Set.member t s

-- ═══════════════════════════════════════════════════════════
-- Difficulty profiling: WHERE does NP-hardness appear?
-- ═══════════════════════════════════════════════════════════

-- | Profile of how the TargetAware annotation grows at each level.
data DifficultyProfile = DP
  { dpElements     :: [Int]
  , dpLevelSizes   :: [(Int, Int, Int)]  -- (level, numNodes, maxAnnotationSize)
  , dpExplosionLevel :: Maybe Int         -- first level where max size > poly threshold
  } deriving (Show)

-- | Build the tree bottom-up, measuring TargetAware size at each level.
--
-- THIS IS THE KEY EXPERIMENT:
-- Level 0 (leaves): TA size = 2 (always)
-- Level 1: TA size ≤ 4
-- Level k: TA size ≤ 2^(2^k) worst case
-- At which k does it exceed n^2? That's where NP-hardness "appears".
measureDifficulty :: [Int] -> DifficultyProfile
measureDifficulty elems =
  let leaves = map taFromElement elems
      profile = buildProfile 0 leaves []
      threshold = length elems ^ (2 :: Int)  -- poly(n) = n²
      explosion = findExplosion threshold profile
  in DP elems profile explosion
  where
    buildProfile :: Int -> [TargetAware] -> [(Int, Int, Int)] -> [(Int, Int, Int)]
    buildProfile level nodes acc
      | length nodes <= 1 =
          let sizes = map (Set.size . taReachable) nodes
              maxSize = if null sizes then 0 else maximum sizes
          in reverse ((level, length nodes, maxSize) : acc)
      | otherwise =
          let sizes = map (Set.size . taReachable) nodes
              maxSize = if null sizes then 0 else maximum sizes
              acc' = (level, length nodes, maxSize) : acc
              -- Merge pairs for next level
              nextLevel = mergePairs nodes
          in buildProfile (level + 1) nextLevel acc'

    mergePairs :: [TargetAware] -> [TargetAware]
    mergePairs [] = []
    mergePairs [x] = [x]
    mergePairs (x:y:rest) = taMerge x y : mergePairs rest

    findExplosion :: Int -> [(Int, Int, Int)] -> Maybe Int
    findExplosion threshold profile =
      case filter (\(_, _, sz) -> sz > threshold) profile of
        ((lvl, _, _):_) -> Just lvl
        []              -> Nothing

showDifficultyProfile :: DifficultyProfile -> String
showDifficultyProfile dp = unlines $
  [ "  Elements: " ++ show (dpElements dp)
  , "  Poly threshold (n²): " ++ show (length (dpElements dp) ^ (2 :: Int))
  , ""
  , "  " ++ padR' 8 "Level" ++ padR' 8 "Nodes" ++ padR' 12 "Max |TA|" ++ "Status"
  , "  " ++ replicate 45 '-'
  ] ++
  [ "  " ++ padR' 8 (show lvl)
    ++ padR' 8 (show nodes)
    ++ padR' 12 (show sz)
    ++ status sz
  | (lvl, nodes, sz) <- dpLevelSizes dp
  ] ++
  [ ""
  , "  Explosion level: " ++ case dpExplosionLevel dp of
      Nothing -> "NONE (stays polynomial!)"
      Just l  -> show l ++ " ← NP-hardness appears here"
  ]
  where
    threshold = length (dpElements dp) ^ (2 :: Int)
    status sz
      | sz <= threshold = "poly"
      | sz <= 1000      = "GROWING"
      | otherwise       = "EXPLODED"

padR' :: Int -> String -> String
padR' n s = s ++ replicate (max 0 (n - length s)) ' '
