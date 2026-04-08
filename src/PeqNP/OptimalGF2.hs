module PeqNP.OptimalGF2
  ( -- * Deep GF(2) search
    deepSearch
  , beamSearch
  , DeepSearchResult(..)
  , showDeepSearchResult
    -- * Iterative greedy reduction
  , iterativeGreedyReduce
  , showIterativeResult
  ) where

import PeqNP.BitDecompose (weightsToBitMatrix, overlapOfMatrix, xorTransform, BitMatrix)

-- | Result of deep GF(2) search
data DeepSearchResult = DSR
  { dsrOriginalOverlap :: Int
  , dsrBestOverlap     :: Int
  , dsrBestOps         :: [(Int, Int)]  -- (target_col, source_col) XOR ops
  , dsrDepthSearched   :: Int
  , dsrStatesExplored  :: Int
  } deriving (Show)

-- | Deep search: BFS/DFS over sequences of column XOR operations.
-- At each step, try ALL possible (col_i ^= col_j) and keep the best.
-- Depth k means up to k sequential XOR operations.
deepSearch :: Int -> [Int] -> DeepSearchResult
deepSearch maxDepth elems =
  let mat = weightsToBitMatrix elems
      cols = if null mat then 0 else length (head mat)
      origOverlap = overlapOfMatrix mat
      -- All possible single operations
      allOps = [(i, j) | i <- [0..cols-1], j <- [0..cols-1], i /= j]
      -- BFS: at each depth, try all ops on the best matrices from previous depth
      (bestOv, bestOps, explored) = bfs maxDepth mat allOps origOverlap [] 0
  in DSR
    { dsrOriginalOverlap = origOverlap
    , dsrBestOverlap     = bestOv
    , dsrBestOps         = bestOps
    , dsrDepthSearched   = maxDepth
    , dsrStatesExplored  = explored
    }

bfs :: Int -> BitMatrix -> [(Int,Int)] -> Int -> [(Int,Int)] -> Int -> (Int, [(Int,Int)], Int)
bfs 0 _ _ bestOv bestOps explored = (bestOv, bestOps, explored)
bfs depth mat allOps bestOv bestOps explored =
  let -- Try every single operation on current matrix
      results = [ (overlapOfMatrix mat', op)
                | op@(i, j) <- allOps
                , let mat' = xorTransform mat [(i, [j])]
                ]
      -- Find the best single operation
      (bestSingleOv, bestSingleOp) = foldr
        (\(ov, op) (bov, bop) -> if ov < bov then (ov, op) else (bov, bop))
        (bestOv, (0,0)) results
      explored' = explored + length results
  in if bestSingleOv < bestOv
     then
       -- Found improvement: apply it and recurse deeper
       let mat' = xorTransform mat [(fst bestSingleOp, [snd bestSingleOp])]
           newOps = bestOps ++ [bestSingleOp]
       in bfs (depth - 1) mat' allOps bestSingleOv newOps explored'
     else
       -- No improvement: stop
       (bestOv, bestOps, explored')

-- | Beam search: keep top-k candidates at each depth level.
-- More thorough than greedy (which keeps only top-1).
beamSearch :: Int -> Int -> [Int] -> DeepSearchResult
beamSearch beamWidth maxDepth elems =
  let mat = weightsToBitMatrix elems
      cols = if null mat then 0 else length (head mat)
      origOverlap = overlapOfMatrix mat
      allOps = [(i, j) | i <- [0..cols-1], j <- [0..cols-1], i /= j]
      -- Beam: list of (overlap, matrix, ops_so_far)
      initialBeam = [(origOverlap, mat, [] :: [(Int,Int)])]
      finalBeam = doBeam maxDepth beamWidth allOps initialBeam 0
      (bestOv, _, bestOps) = minimum' finalBeam
  in DSR
    { dsrOriginalOverlap = origOverlap
    , dsrBestOverlap     = bestOv
    , dsrBestOps         = bestOps
    , dsrDepthSearched   = maxDepth
    , dsrStatesExplored  = maxDepth * beamWidth * length allOps
    }

doBeam :: Int -> Int -> [(Int,Int)] -> [(Int, BitMatrix, [(Int,Int)])] -> Int -> [(Int, BitMatrix, [(Int,Int)])]
doBeam 0 _ _ beam _ = beam
doBeam depth width allOps beam explored =
  let -- Expand each beam candidate by all ops
      expanded = [ (overlapOfMatrix mat', mat', ops ++ [op])
                 | (_, m, ops) <- beam
                 , op@(i, j) <- allOps
                 , let mat' = xorTransform m [(i, [j])]
                 ]
      -- Keep top-width by overlap
      sorted = sortByOverlap expanded
      topK = take width sorted
  in doBeam (depth - 1) width allOps topK (explored + length expanded)

sortByOverlap :: [(Int, a, b)] -> [(Int, a, b)]
sortByOverlap [] = []
sortByOverlap (x@(ov,_,_):xs) =
  sortByOverlap [y | y@(ov',_,_) <- xs, ov' <= ov]
  ++ [x]
  ++ sortByOverlap [y | y@(ov',_,_) <- xs, ov' > ov]

minimum' :: [(Int, a, b)] -> (Int, a, b)
minimum' [x] = x
minimum' (x@(ov1,_,_):y@(ov2,_,_):rest) =
  if ov1 <= ov2 then minimum' (x:rest) else minimum' (y:rest)
minimum' [] = error "empty beam"

-- ═══════════════════════════════════════════════════════════
-- Iterative greedy: apply the best XOR repeatedly
-- ═══════════════════════════════════════════════════════════

-- | Apply the greedy-best XOR operation repeatedly until no improvement.
-- Track overlap at each step to see the convergence curve.
iterativeGreedyReduce :: [Int] -> [(Int, (Int, Int))]
iterativeGreedyReduce elems =
  let mat = weightsToBitMatrix elems
  in go mat (overlapOfMatrix mat) []
  where
    go mat currentOv acc =
      let cols = if null mat then 0 else length (head mat)
          candidates = [ (overlapOfMatrix (xorTransform mat [(i,[j])]), (i,j))
                       | i <- [0..cols-1], j <- [0..cols-1], i /= j
                       ]
          (bestOv, bestOp) = foldr
            (\(ov,op) (bov,bop) -> if ov < bov then (ov,op) else (bov,bop))
            (currentOv, (0,0)) candidates
      in if bestOv < currentOv
         then go (xorTransform mat [(fst bestOp, [snd bestOp])]) bestOv
                 (acc ++ [(bestOv, bestOp)])
         else acc  -- converged

showDeepSearchResult :: DeepSearchResult -> String
showDeepSearchResult dsr = unlines
  [ "  Original overlap: " ++ show (dsrOriginalOverlap dsr)
  , "  Best overlap:     " ++ show (dsrBestOverlap dsr)
  , "  Reduction:        " ++ show (dsrOriginalOverlap dsr) ++ " → " ++ show (dsrBestOverlap dsr)
      ++ " (" ++ show (length (dsrBestOps dsr)) ++ " operations)"
  , "  Depth searched:   " ++ show (dsrDepthSearched dsr)
  , "  States explored:  " ++ show (dsrStatesExplored dsr)
  ]

showIterativeResult :: [Int] -> String
showIterativeResult elems =
  let steps = iterativeGreedyReduce elems
      overlaps = overlapOfMatrix (weightsToBitMatrix elems) : map fst steps
  in unlines
    [ "  Convergence: " ++ show overlaps
    , "  Steps: " ++ show (length steps)
    , "  Final overlap: " ++ show (if null steps then overlapOfMatrix (weightsToBitMatrix elems) else fst (last steps))
    ]
