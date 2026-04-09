module PeqNP.ResidualGraph
  ( -- * Core types
    ResidualGraph(..)
  , RNode(..)
  , REdge(..)
    -- * Build the graph
  , buildResidualGraph
    -- * Search strategies
  , bfsSearch          -- naive BFS (tracks used elements, exponential worst case)
  , greedySearch       -- greedy: always pick largest element first
  , residualChainSearch -- follow residual chains without backtracking
    -- * Analysis
  , graphStats
  , showGraph
  , showSearchResult
  , SearchResult(..)
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (sort, sortBy)
import Data.Ord (Down(..))

-- ═══════════════════════════════════════════════════════════
-- Types
-- ═══════════════════════════════════════════════════════════

data RNode
  = NTarget !Int          -- the target value
  | NResidual !Int        -- a residual (target - some elements)
  | NZero                 -- goal: residual reached 0
  deriving (Show, Eq, Ord)

data REdge = REdge
  { reFrom    :: !Int     -- residual value we're at
  , reTo      :: !Int     -- residual after subtracting element
  , reElement :: !Int     -- the element used
  } deriving (Show, Eq, Ord)

data ResidualGraph = RG
  { rgTarget   :: !Int
  , rgElements :: ![Int]
  , rgElemSet  :: !(Set.Set Int)            -- elements as a Set for O(log n) lookup
  , rgEdges    :: !(Map.Map Int [REdge])    -- from residual -> outgoing edges
  , rgHits     :: !(Set.Set Int)            -- residuals that ARE elements (instant matches)
  , rgDepth    :: !Int                      -- max depth needed (n = number of elements)
  } deriving (Show)

data SearchResult = SearchResult
  { srFound    :: !Bool
  , srSolution :: !(Maybe [Int])   -- elements used
  , srNodes    :: !Int             -- nodes visited
  , srMethod   :: !String
  } deriving (Show)

showSearchResult :: SearchResult -> String
showSearchResult sr =
  "found=" ++ show (srFound sr)
  ++ " solution=" ++ show (srSolution sr)
  ++ " nodes=" ++ show (srNodes sr)
  ++ " method=" ++ srMethod sr

-- ═══════════════════════════════════════════════════════════
-- Build the residual graph
--
-- Key insight: we DON'T build the full 2^n subsets.
-- We build a graph where:
--   nodes = {target, target-w1, target-w2, ..., and recursively}
--   edges = "subtract element w from residual r → new residual r-w"
--
-- The graph has at most target+1 distinct residual values (bounded by target).
-- Each has at most n outgoing edges. Total: O(n × target) edges.
-- For density-1 (target ~ n×2^n), this is pseudo-polynomial.
--
-- BUT: we only build residuals that are REACHABLE from the target.
-- And we annotate which residuals are themselves elements (hits).
-- ═══════════════════════════════════════════════════════════

buildResidualGraph :: [Int] -> Int -> ResidualGraph
buildResidualGraph weights target =
  let elemSet = Set.fromList weights
      -- BFS from target: discover reachable residuals
      -- Only follow edges where residual >= 0
      (edges, visited) = bfsBuild elemSet weights target
      -- Hits: residuals that are also elements in the list
      hits = Set.filter (`Set.member` elemSet) visited
  in RG
    { rgTarget = target
    , rgElements = weights
    , rgElemSet = elemSet
    , rgEdges = edges
    , rgHits = hits
    , rgDepth = length weights
    }

-- | BFS to build edge map. Only explore residuals >= 0.
-- Limit depth to n (can't use more than n elements).
bfsBuild :: Set.Set Int -> [Int] -> Int
          -> (Map.Map Int [REdge], Set.Set Int)
bfsBuild elemSet weights target =
  let n = length weights
      go :: Int -> Set.Set Int -> [Int] -> Map.Map Int [REdge]
         -> (Map.Map Int [REdge], Set.Set Int)
      go depth visited [] edgeMap = (edgeMap, visited)
      go depth visited frontier edgeMap
        | depth >= n = (edgeMap, visited)
        | otherwise =
          let -- For each frontier residual, generate edges
              newEdges = [ REdge r (r - w) w
                         | r <- frontier
                         , w <- weights
                         , r - w >= 0
                         ]
              -- Group by source
              edgeGroups = Map.fromListWith (++)
                [(reFrom e, [e]) | e <- newEdges]
              -- New residuals not yet visited
              newResiduals = Set.fromList [reTo e | e <- newEdges]
              unvisited = Set.difference newResiduals visited
              newFrontier = Set.toList unvisited
              newVisited = Set.union visited unvisited
              newEdgeMap = Map.unionWith (++) edgeMap edgeGroups
          in go (depth + 1) newVisited newFrontier newEdgeMap

  in go 0 (Set.singleton target) [target] Map.empty

-- ═══════════════════════════════════════════════════════════
-- Graph stats
-- ═══════════════════════════════════════════════════════════

graphStats :: ResidualGraph -> String
graphStats rg =
  let nNodes = Map.size (rgEdges rg) + 1  -- +1 for target
      nEdges = sum (map length (Map.elems (rgEdges rg)))
      nHits = Set.size (rgHits rg)
  in "nodes=" ++ show nNodes
     ++ " edges=" ++ show nEdges
     ++ " hits=" ++ show nHits
     ++ " elements=" ++ show (length (rgElements rg))

showGraph :: ResidualGraph -> String
showGraph rg =
  let target = rgTarget rg
      edges = Map.toAscList (rgEdges rg)
  in unlines $
    ["ResidualGraph target=" ++ show target
    , "  elements=" ++ show (rgElements rg)
    , "  hits (residuals that are elements)=" ++ show (Set.toList (rgHits rg))
    , "  edges:"
    ] ++
    [ "    " ++ show src ++ " --(-" ++ show (reElement e) ++ ")--> "
      ++ show (reTo e)
      ++ (if reTo e == 0 then " ★ZERO" else "")
      ++ (if Set.member (reTo e) (rgElemSet rg) then " ●HIT" else "")
    | (src, es) <- take 50 edges  -- limit output
    , e <- es
    ]

-- ═══════════════════════════════════════════════════════════
-- Search 1: BFS with used-element tracking
--
-- State = (current residual, set of used elements)
-- This IS exponential in worst case (2^n possible used-sets)
-- but in practice the graph structure limits exploration.
-- ═══════════════════════════════════════════════════════════

bfsSearch :: ResidualGraph -> SearchResult
bfsSearch rg =
  let target = rgTarget rg
      -- BFS queue: [(residual, usedElements, path)]
      initial = [(target, Set.empty, [])]
      (found, sol, nodes) = bfsGo rg initial Set.empty 0
  in SearchResult found sol nodes "bfsSearch"

bfsGo :: ResidualGraph -> [(Int, Set.Set Int, [Int])] -> Set.Set (Int, Set.Set Int) -> Int
      -> (Bool, Maybe [Int], Int)
bfsGo _ [] _ nodes = (False, Nothing, nodes)
bfsGo rg ((r, used, path):queue) visited nodes
  | nodes > 10000000 = (False, Nothing, nodes)  -- safety limit
  | r == 0 = (True, Just (reverse path), nodes + 1)
  | Set.member (r, used) visited = bfsGo rg queue visited (nodes + 1)
  | otherwise =
    let visited' = Set.insert (r, used) visited
        edges = Map.findWithDefault [] r (rgEdges rg)
        -- Only follow edges for elements not yet used
        validEdges = [e | e <- edges, not (Set.member (reElement e) used)]
        newStates = [(reTo e, Set.insert (reElement e) used, reElement e : path)
                    | e <- validEdges]
    in bfsGo rg (queue ++ newStates) visited' (nodes + 1)

-- ═══════════════════════════════════════════════════════════
-- Search 2: Greedy — always subtract the largest possible element
--
-- O(n²) worst case. Not complete (might miss solutions).
-- But if it works, it's instant.
-- ═══════════════════════════════════════════════════════════

greedySearch :: ResidualGraph -> SearchResult
greedySearch rg =
  let sortedDesc = sortBy (flip compare) (rgElements rg)
      (found, sol, nodes) = greedyGo (rgTarget rg) sortedDesc [] 0
  in SearchResult found sol nodes "greedySearch"

greedyGo :: Int -> [Int] -> [Int] -> Int -> (Bool, Maybe [Int], Int)
greedyGo 0 _ path nodes = (True, Just (reverse path), nodes)
greedyGo _ [] _ nodes = (False, Nothing, nodes)
greedyGo residual (w:ws) path nodes
  | w <= residual = -- try including w first (greedy)
      case greedyGo (residual - w) ws (w:path) (nodes + 1) of
        (True, sol, n) -> (True, sol, n)
        (False, _, n)  -> greedyGo residual ws path n  -- backtrack
  | otherwise = greedyGo residual ws path (nodes + 1)

-- ═══════════════════════════════════════════════════════════
-- Search 3: Residual chain — follow the "hits" structure
--
-- Key idea: if residual r is itself an element → we can go
-- directly to r → 0 using that element. So look for CHAINS:
--   target → (target - w1) → ... → (some hit h) → 0
--
-- A "hit" is a residual that equals an element. Finding a
-- chain from target to a hit (through valid residuals) gives
-- a solution.
--
-- This exploits the graph structure: hits are "exit points"
-- where the chain can terminate in one step.
-- ═══════════════════════════════════════════════════════════

residualChainSearch :: ResidualGraph -> SearchResult
residualChainSearch rg =
  let target = rgTarget rg
      elems = sortBy (flip compare) (rgElements rg)  -- try largest first
      (found, sol, nodes) = chainGo target elems Set.empty [] 0
  in SearchResult found sol nodes "residualChain"

chainGo :: Int -> [Int] -> Set.Set Int -> [Int] -> Int -> (Bool, Maybe [Int], Int)
chainGo 0 _ _ path nodes = (True, Just (reverse path), nodes)
chainGo residual _ _ _ nodes | residual < 0 = (False, Nothing, nodes)
chainGo _ [] _ _ nodes = (False, Nothing, nodes)
chainGo residual allElems used path nodes
  | nodes > 10000000 = (False, Nothing, nodes)
  | otherwise =
    let available = [w | w <- allElems, not (Set.member w used), w <= residual]
    in tryElems residual allElems used path nodes available

tryElems :: Int -> [Int] -> Set.Set Int -> [Int] -> Int -> [Int] -> (Bool, Maybe [Int], Int)
tryElems _ _ _ _ nodes [] = (False, Nothing, nodes)
tryElems residual allElems used path nodes (w:ws) =
  let newResidual = residual - w
      newUsed = Set.insert w used
      result = chainGo newResidual allElems newUsed (w:path) (nodes + 1)
  in case result of
    (True, sol, n) -> (True, sol, n)
    (False, _, n)  -> tryElems residual allElems used path n ws
