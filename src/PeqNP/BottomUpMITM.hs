module PeqNP.BottomUpMITM
  ( -- * Main solver
    bottomUpSolve
  , BUResult(..)
  , showBUResult
    -- * Memoized solver (counts distinct states)
  , bottomUpSolveMemo
  , MemoResult(..)
  , showMemoResult
    -- * Match types for solution reconstruction
  , BUMatchType(..)
    -- * Internals (for testing)
  , pairCheck
  , pairFind
  , buildSuffixSets
  , buildSuffixCounts
  ) where

import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import Data.List (foldl')
import Data.Array (Array, listArray, (!))
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import PeqNP.OracleSolver (SuffixOracles, buildOracles, queryOracle)

-- ═══════════════════════════════════════════════════════════
-- BottomUpMITM: Branch-and-Bound with cardinality-bounded
-- reachable set checks at every node.
--
-- Key insight (from user): each subtree's reachable sums
-- can be checked ON-THE-FLY without precomputing the full
-- exponential set. For bounded cardinality k:
--
--   k=1 (singleton): is residual r one of the remaining elements?
--   k=2 (pair):      is r = a + b for some a, b in remaining?
--
-- Combined with complement trick:
--   k=1 complement:  is (suffixSum - r) a single element?
--                    ↔ solution uses all-but-one of suffix
--   k=2 complement:  is (suffixSum - r) = a + b?
--                    ↔ solution uses all-but-two of suffix
--
-- With k=2, this covers cardinality bands {0,1,2} and
-- {n-d-2, n-d-1, n-d}. For suffixes of ≤4 elements,
-- this is COMPLETE (exact answer, no search needed).
--
-- The gap (middle cardinalities) is covered by modular
-- suffix oracles from OracleSolver (O(1) per query).
--
-- Per-node cost: O(n) for k=2. Precompute: O(n²) total.
-- This is strictly better than LazyTree (no bottom-up info)
-- and OracleSolver (modular only, no exact cardinality).
-- ═══════════════════════════════════════════════════════════

-- | How the solution was found.
data BUMatchType
  = BUSingleton       -- ^ residual matched a single suffix element
  | BUPair            -- ^ residual matched a pair of suffix elements
  | BUComplSingleton  -- ^ complement residual matched a singleton (all-but-one)
  | BUComplPair       -- ^ complement residual matched a pair (all-but-two)
  | BUExact           -- ^ residual was exactly 0
  | BURecursive       -- ^ found via full recursive search (gap region)
  deriving (Show, Eq)

-- | Result of bottom-up MITM solver.
data BUResult = BUResult
  { buFound         :: !Bool
  , buSolution      :: !(Maybe [Int])
  , buMatchType     :: !(Maybe BUMatchType)
  , buNodesExplored :: !Int
  , buSingletonHits :: !Int    -- solutions/prunes from singleton check
  , buPairHits      :: !Int    -- solutions/prunes from pair check
  , buComplHits     :: !Int    -- solutions/prunes from complement checks
  , buOracleHits    :: !Int    -- prunes from modular oracle
  , buBoundHits     :: !Int    -- prunes from standard bounds
  } deriving (Show)

showBUResult :: BUResult -> String
showBUResult r =
  "found=" ++ show (buFound r)
  ++ " nodes=" ++ show (buNodesExplored r)
  ++ " match=" ++ maybe "none" show (buMatchType r)
  ++ " [sing=" ++ show (buSingletonHits r)
  ++ " pair=" ++ show (buPairHits r)
  ++ " compl=" ++ show (buComplHits r)
  ++ " oracle=" ++ show (buOracleHits r)
  ++ " bound=" ++ show (buBoundHits r) ++ "]"
  ++ case buSolution r of
       Just sol -> " solution=" ++ show sol
       Nothing  -> ""

-- ═══════════════════════════════════════════════════════════
-- Precomputed suffix data structures
-- ═══════════════════════════════════════════════════════════

-- | Suffix element sets: suffixSets[d] = IntSet of elements[d..n-1].
-- Used for O(1) singleton membership and O(n) pair checking.
-- Built incrementally right-to-left in O(n log n).
buildSuffixSets :: [Int] -> Array Int IS.IntSet
buildSuffixSets weights =
  let n = length weights
      indexed = zip [0..] weights
      -- Build from right: start empty, insert each element
      sets = scanr (\(_, w) acc -> IS.insert w acc) IS.empty indexed
  in listArray (0, n) sets  -- suffixSets[d] = elements d..n-1; suffixSets[n] = empty

-- | Suffix element counts: for handling duplicates in pair check.
-- suffixCounts[d] = IntMap from element value → count in elements[d..n-1].
buildSuffixCounts :: [Int] -> Array Int (IM.IntMap Int)
buildSuffixCounts weights =
  let n = length weights
      indexed = zip [0..] weights
      counts = scanr (\(_, w) acc -> IM.insertWith (+) w 1 acc) IM.empty indexed
  in listArray (0, n) counts

-- | Suffix sums: suffixSums[d] = sum(elements[d..n-1]).
buildSuffixSums :: [Int] -> Array Int Int
buildSuffixSums weights =
  let n = length weights
      sums = scanr (+) 0 weights
  in listArray (0, n) sums

-- ═══════════════════════════════════════════════════════════
-- Pair checking: O(n) per query
--
-- Given target sum r and the set of available elements,
-- check if any pair (a, b) with a + b = r exists.
-- Handles duplicates: if r = 2a, need count(a) ≥ 2.
-- ═══════════════════════════════════════════════════════════

-- | Check if r is achievable as a sum of two elements from the suffix.
-- Returns True if ∃ a, b in suffix: a + b = r (a and b may be equal if count ≥ 2).
pairCheck :: Int -> IS.IntSet -> IM.IntMap Int -> Bool
pairCheck r elemSet elemCounts =
  any (\v -> let complement = r - v
             in if complement == v
                then IM.findWithDefault 0 v elemCounts >= 2
                else IS.member complement elemSet
      ) (IS.toAscList elemSet)

-- | Find a pair (a, b) with a + b = r. Returns Just (a, b) or Nothing.
pairFind :: Int -> IS.IntSet -> IM.IntMap Int -> Maybe (Int, Int)
pairFind r elemSet elemCounts =
  go (IS.toAscList elemSet)
  where
    go [] = Nothing
    go (v:vs) =
      let complement = r - v
      in if complement == v
         then if IM.findWithDefault 0 v elemCounts >= 2
              then Just (v, v)
              else go vs
         else if IS.member complement elemSet
              then Just (v, complement)
              else go vs

-- ═══════════════════════════════════════════════════════════
-- Triple checking: O(n²) per query
--
-- Check if r = a + b + c for three elements in the suffix.
-- With complement trick: also checks all-but-three subsets.
-- ═══════════════════════════════════════════════════════════

-- | Check if r is achievable as a sum of three elements from the suffix.
-- O(n²): for each element a, do a pair check on (r - a) in remaining.
tripleCheck :: Int -> IS.IntSet -> IM.IntMap Int -> Bool
tripleCheck r elemSet elemCounts =
  any (\a ->
    let r' = r - a
        -- Remove one copy of a from the available set
        set' = IS.delete a elemSet
        cnt' = IM.update (\c -> if c > 1 then Just (c - 1) else Nothing) a elemCounts
    in r' > 0 && pairCheck r' set' cnt'
  ) (IS.toAscList elemSet)

-- ═══════════════════════════════════════════════════════════
-- Big oracles: larger primes for better pruning in deep suffixes
--
-- The standard oracles use primes [37..61] with Word64 bitsets.
-- These fill up quickly for suffixes > 6 elements.
-- Big oracles use primes [127, 251, 509, 1021] with IntSet.
-- They stay effective for suffixes up to ~10 elements.
-- Cost: O(n × Σp) ≈ O(2000n) to build. O(1) per query.
-- ═══════════════════════════════════════════════════════════

bigOraclePrimes :: [Int]
bigOraclePrimes = [127, 251, 509, 1021, 2053, 4099, 8209, 16411, 32771, 65537]

-- | Big suffix oracles: oracles[d][j] = IntSet of reachable residues mod prime j
-- for suffix elements[d..n-1].
type BigSuffixOracles = [[IS.IntSet]]

-- | Build big suffix oracles. O(n × Σp).
buildBigOracles :: [Int] -> BigSuffixOracles
buildBigOracles weights =
  let emptyBitsets = [IS.singleton 0 | _ <- bigOraclePrimes]
      go :: [[IS.IntSet]] -> [Int] -> [[IS.IntSet]]
      go acc [] = acc
      go (current:rest) (w:ws) =
        let updated = zipWith (addElemBig w) bigOraclePrimes current
        in go (updated : current : rest) ws
      go [] _ = []
  in go [emptyBitsets] (reverse weights)

-- | Add an element to a big oracle bitset.
addElemBig :: Int -> Int -> IS.IntSet -> IS.IntSet
addElemBig w p bitset =
  let wModP = w `mod` p
      shifted = IS.fromList [(r + wModP) `mod` p | r <- IS.toList bitset]
  in IS.union bitset shifted

-- | Query big oracle: is residual achievable mod all big primes?
queryBigOracle :: BigSuffixOracles -> Int -> Int -> Bool
queryBigOracle oracles depth residual =
  let sets = oracles !! depth
  in all (\(p, s) -> IS.member (residual `mod` p) s)
         (zip bigOraclePrimes sets)

-- ═══════════════════════════════════════════════════════════
-- Main solver
-- ═══════════════════════════════════════════════════════════

-- | Bottom-up MITM solver with cardinality-bounded reachable checks.
--
-- @maxK@ controls the maximum cardinality for exact checks:
--   1 = singleton only (O(1) per node)
--   2 = singleton + pair (O(n) per node) — recommended
--   (Higher k is possible but increases per-node cost to O(n^{k-1}))
--
-- Three pruning layers at each node:
--   Layer 1: Standard bounds (overshoot / undershoot)
--   Layer 2: Cardinality-exact + complement (YOUR IDEA)
--   Layer 3: Modular suffix oracles (gap coverage)
bottomUpSolve :: Int -> [Int] -> Int -> BUResult
bottomUpSolve maxK weights target =
  let n         = length weights
      wArr      = listArray (0, n-1) weights
      suffSets  = buildSuffixSets weights
      suffCnts  = buildSuffixCounts weights
      suffSums  = buildSuffixSums weights
      oracles   = buildOracles weights

      -- Core recursive search
      -- Returns (found, solution, matchType, nodes, singH, pairH, complH, oracleH, boundH)
      search :: Int -> Int -> [Int]
             -> (Bool, Maybe [Int], Maybe BUMatchType, Int, Int, Int, Int, Int, Int)
      search depth partialSum included
        -- Base case: no more elements
        | depth >= n =
            if partialSum == target
            then (True, Just (reverse included), Just BUExact, 1, 0, 0, 0, 0, 0)
            else (False, Nothing, Nothing, 1, 0, 0, 0, 0, 0)

        | otherwise =
            let r       = target - partialSum
                suffSum = suffSums ! depth
                eSet    = suffSets ! depth
                eCnts   = suffCnts ! depth
                w       = wArr ! depth

            in -- Layer 1: Standard bounds
               if r < 0 then (False, Nothing, Nothing, 1, 0, 0, 0, 0, 1)
               else if r > suffSum then (False, Nothing, Nothing, 1, 0, 0, 0, 0, 1)

               -- Exact: residual is 0 (already at target)
               else if r == 0 then
                 (True, Just (reverse included), Just BUExact, 1, 0, 0, 0, 0, 0)

               -- Layer 2: Cardinality-exact checks
               -- Singleton: r is a single remaining element
               else if maxK >= 1 && IS.member r eSet then
                 (True, Just (reverse (r : included)), Just BUSingleton, 1, 1, 0, 0, 0, 0)

               -- Complement singleton: suffixSum - r is a single element
               -- means: take ALL suffix elements EXCEPT that one
               else if maxK >= 1 && r /= suffSum && IS.member (suffSum - r) eSet then
                 let excluded = suffSum - r
                     sol = reverse included ++ removeOne excluded (suffixElems depth n wArr)
                 in (True, Just sol, Just BUComplSingleton, 1, 0, 0, 1, 0, 0)

               -- Pair: r = a + b for two remaining elements
               else if maxK >= 2 then
                 case pairFind r eSet eCnts of
                   Just (a, b) ->
                     (True, Just (reverse included ++ [a, b]), Just BUPair, 1, 0, 1, 0, 0, 0)
                   Nothing ->
                     -- Complement pair: suffixSum - r = a + b
                     let cr = suffSum - r
                     in if cr >= 0 then
                          case pairFind cr eSet eCnts of
                            Just (a, b) ->
                              let suffElems = suffixElems depth n wArr
                                  remaining = if a == b
                                              then removeTwo a suffElems
                                              else filterOut a b suffElems
                                  sol = reverse included ++ remaining
                              in (True, Just sol, Just BUComplPair, 1, 0, 0, 1, 0, 0)
                            Nothing -> continueSearch depth r w partialSum included
                                         oracles n wArr suffSets suffCnts suffSums maxK
                        else continueSearch depth r w partialSum included
                               oracles n wArr suffSets suffCnts suffSums maxK

               -- k=1 only: skip pair checks, go to oracle
               else continueSearch depth r w partialSum included
                      oracles n wArr suffSets suffCnts suffSums maxK

      -- After exact checks fail: try oracle, then recurse
      continueSearch depth r w partialSum included
                     oracls _nElem _wArray _sSets _sCnts _sSums _mK =
        let -- Layer 3: Modular oracle pruning (per-branch)
            canInclude = r - w >= 0 && queryOracle oracls (depth + 1) (r - w)
            canExclude = queryOracle oracls (depth + 1) r
        in if not canInclude && not canExclude
           then (False, Nothing, Nothing, 1, 0, 0, 0, 1, 0)
           else
             -- Try include branch first (greedily try to reach target)
             let (f1, s1, m1, n1, sh1, ph1, ch1, oh1, bh1) =
                   if canInclude
                   then search (depth+1) (partialSum + w) (w : included)
                   else (False, Nothing, Nothing, 0, 0, 0, 0, 1, 0)
             in if f1
                then (True, s1, m1, n1+1, sh1, ph1, ch1, oh1, bh1)
                else
                  let (f2, s2, m2, n2, sh2, ph2, ch2, oh2, bh2) =
                        if canExclude
                        then search (depth+1) partialSum included
                        else (False, Nothing, Nothing, 0, 0, 0, 0, 1, 0)
                  in ( f2, s2, m2
                     , n1 + n2 + 1
                     , sh1 + sh2, ph1 + ph2, ch1 + ch2
                     , oh1 + oh2, bh1 + bh2 )

      (found, sol, mt, nodes, sH, pH, cH, oH, bH) = search 0 0 []

  in BUResult
    { buFound         = found
    , buSolution      = sol
    , buMatchType     = mt
    , buNodesExplored = nodes
    , buSingletonHits = sH
    , buPairHits      = pH
    , buComplHits     = cH
    , buOracleHits    = oH
    , buBoundHits     = bH
    }

-- ═══════════════════════════════════════════════════════════
-- Utilities
-- ═══════════════════════════════════════════════════════════

-- | Get suffix elements as list (for solution reconstruction).
suffixElems :: Int -> Int -> Array Int Int -> [Int]
suffixElems depth n wArr = [wArr ! i | i <- [depth..n-1]]

-- | Remove exactly one occurrence of a value from a list.
removeOne :: Int -> [Int] -> [Int]
removeOne _ [] = []
removeOne v (x:xs)
  | x == v    = xs
  | otherwise = x : removeOne v xs

-- | Filter out exactly one occurrence of a and one of b from a list.
filterOut :: Int -> Int -> [Int] -> [Int]
filterOut a b = go True True
  where
    go _ _ [] = []
    go ra rb (x:xs)
      | ra && x == a = go False rb xs
      | rb && x == b = go ra False xs
      | otherwise    = x : go ra rb xs

-- | Remove exactly two occurrences of a value from a list.
removeTwo :: Int -> [Int] -> [Int]
removeTwo _ [] = []
removeTwo v xs = go (2 :: Int) xs
  where
    go 0 rest     = rest
    go _ []       = []
    go n' (x:rest)
      | x == v    = go (n'-1) rest
      | otherwise = x : go n' rest

-- ═══════════════════════════════════════════════════════════
-- MEMOIZED SOLVER: cache (depth, residual) → Bool
--
-- THE KEY QUESTION: how many DISTINCT (depth, residual) pairs
-- does the search actually visit? If polynomial → P = NP.
--
-- Memoization means: if two different paths through the tree
-- arrive at the same (depth, residual), we compute only once.
-- The number of distinct pairs IS the effective tree size.
--
-- At depth d, residual = target - partialSum. Different paths
-- can produce the same partialSum (hence same residual).
-- With pruning, many residuals are killed. What survives?
-- ═══════════════════════════════════════════════════════════

data MemoResult = MemoResult
  { mrFound          :: !Bool
  , mrDistinctStates :: !Int    -- unique (depth, residual) pairs
  , mrStatesPerDepth :: ![Int]  -- distinct residuals at each depth
  , mrNodesExplored  :: !Int    -- total visits (including cache hits)
  , mrCacheHits      :: !Int    -- times we reused a cached result
  } deriving (Show)

showMemoResult :: MemoResult -> String
showMemoResult m =
  "found=" ++ show (mrFound m)
  ++ " distinctStates=" ++ show (mrDistinctStates m)
  ++ " nodes=" ++ show (mrNodesExplored m)
  ++ " cacheHits=" ++ show (mrCacheHits m)
  ++ "\n  statesPerDepth=" ++ show (mrStatesPerDepth m)

-- | Memoized bottom-up solver. Caches results for (depth, residual) pairs.
-- Returns the search result plus detailed statistics about distinct states.
--
-- Pruning layers (all three stacked):
--   Layer 1: Standard bounds (overshoot / undershoot)
--   Layer 2: Cardinality-exact + complement:
--     k=1: singleton + compl-singleton
--     k=2: + pair + compl-pair (O(n) per node)
--     k=3: + triple + compl-triple (O(n²) per node)
--   Layer 3: Modular oracles (small primes 37-61 + big primes 127-1021)
bottomUpSolveMemo :: Int -> [Int] -> Int -> MemoResult
bottomUpSolveMemo maxK weights target = unsafePerformIO $ do
  let n         = length weights
      wArr      = listArray (0, n-1) weights
      suffSets  = buildSuffixSets weights
      suffCnts  = buildSuffixCounts weights
      suffSums  = buildSuffixSums weights
      oracles   = buildOracles weights
      bigOracs  = buildBigOracles weights

  -- Mutable cache: (depth, residual) → Bool (found)
  cacheRef    <- newIORef (Map.empty :: Map.Map (Int, Int) Bool)
  nodesRef    <- newIORef (0 :: Int)
  cacheHitRef <- newIORef (0 :: Int)

  let search :: Int -> Int -> IO Bool
      search depth partialSum = do
        modifyIORef' nodesRef (+1)
        let r       = target - partialSum
            suffSum = suffSums ! depth

        -- Layer 1: bounds
        if r < 0 || r > suffSum then return False
        else if r == 0 then return True
        else if depth >= n then return (r == 0)
        else do
          -- Check memo cache
          let key = (depth, r)
          cache <- readIORef cacheRef
          case Map.lookup key cache of
            Just result -> do
              modifyIORef' cacheHitRef (+1)
              return result
            Nothing -> do
              -- Compute and cache
              result <- compute depth partialSum r suffSum
              modifyIORef' cacheRef (Map.insert key result)
              return result

      compute :: Int -> Int -> Int -> Int -> IO Bool
      compute depth partialSum r suffSum = do
        let eSet  = suffSets ! depth
            eCnts = suffCnts ! depth
            w     = wArr ! depth
            cr    = suffSum - r  -- complement residual

        -- Layer 2: cardinality-exact checks (in order of cost)

        -- k=1: singleton (O(1))
        if maxK >= 1 && IS.member r eSet then return True
        else if maxK >= 1 && cr >= 0 && cr /= suffSum && IS.member cr eSet then return True

        -- k=2: pair (O(n))
        else if maxK >= 2 && pairCheck r eSet eCnts then return True
        else if maxK >= 2 && cr >= 0 && pairCheck cr eSet eCnts then return True

        -- k=3: triple (O(n²))
        else if maxK >= 3 && tripleCheck r eSet eCnts then return True
        else if maxK >= 3 && cr >= 0 && tripleCheck cr eSet eCnts then return True

        -- Layer 3: oracle pruning + recurse
        else oracleAndRecurse depth partialSum r w

      oracleAndRecurse :: Int -> Int -> Int -> Int -> IO Bool
      oracleAndRecurse depth partialSum r w = do
        -- Combined oracle: small primes AND big primes
        let oracleOk res = queryOracle oracles (depth + 1) res
                           && queryBigOracle bigOracs (depth + 1) res
            canInclude = r - w >= 0 && oracleOk (r - w)
            canExclude = oracleOk r
        if not canInclude && not canExclude
          then return False
          else do
            incResult <- if canInclude
                         then search (depth + 1) (partialSum + w)
                         else return False
            if incResult then return True
            else if canExclude
                 then search (depth + 1) partialSum
                 else return False

  found <- search 0 0
  cache <- readIORef cacheRef
  nodes <- readIORef nodesRef
  hits  <- readIORef cacheHitRef

  -- Count distinct residuals per depth
  let allKeys = Map.keys cache
      maxDepth = if null allKeys then 0 else maximum (map fst allKeys)
      statesPerDepth = [ length [r' | (d, r') <- allKeys, d == i]
                       | i <- [0..maxDepth] ]

  return MemoResult
    { mrFound          = found
    , mrDistinctStates = Map.size cache
    , mrStatesPerDepth = statesPerDepth
    , mrNodesExplored  = nodes
    , mrCacheHits      = hits
    }
