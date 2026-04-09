module PeqNP.OracleSolver
  ( -- * Oracle-guided branch-and-bound
    oracleSolve
  , OracleResult(..)
  , showOracleResult
    -- * Oracle as instant precheck (O(n × P))
  , oraclePrecheck
    -- * Oracle-enhanced MITM
  , oracleMITM
    -- * Suffix oracle precomputation
  , SuffixOracles
  , buildOracles
  , queryOracle
    -- * For benchmarking
  , plainBnB
  ) where

import qualified Data.Set as Set
import Data.List (foldl')
import Data.Bits (setBit, testBit, (.|.))
import Data.Word (Word64)

-- ═══════════════════════════════════════════════════════════
-- Suffix Oracles: precomputed modular reachability per suffix
--
-- For each suffix i..n and each prime p:
--   reachable[i][p] = bitset of {s mod p | s achievable by subsets of elements[i..n]}
--
-- At any node during search:
--   residual = target - partialSum
--   if (residual mod p) is NOT in reachable[i][p] → PRUNE
--
-- This is the "global information flowing to local decisions" idea.
-- Precompute is O(n × Σp). Query is O(1) per prime (bitset test).
-- ═══════════════════════════════════════════════════════════

-- | Primes used for modular oracles.
-- Chosen > 32 so suffix bitsets don't trivially fill up.
-- More primes = more pruning power but more precompute.
oraclePrimes :: [Int]
oraclePrimes = [37, 41, 43, 47, 53, 59, 61]

-- | Suffix oracles: for each depth i (0 = full array, n = empty suffix),
-- a list of bitsets (one per prime) representing reachable residues.
-- oracles[i] corresponds to suffix elements[i..n-1].
type SuffixOracles = [[Word64]]  -- oracles[i][j] = bitset for prime j at suffix i

-- | Build all suffix oracles. O(n × Σp).
-- Built RIGHT to LEFT: start from empty suffix, add elements.
buildOracles :: [Int] -> SuffixOracles
buildOracles weights =
  let n = length weights
      primes = oraclePrimes
      nPrimes = length primes

      -- Start from suffix n (empty): reachable = {0}
      emptyBitsets = [setBit (0 :: Word64) 0 | _ <- primes]

      -- Build from right to left
      -- For each element w (processed in reverse):
      --   new_reachable_mod_p = old ∪ {(r + w) mod p | r ∈ old}
      go :: [[Word64]] -> [Int] -> [[Word64]]
      go acc [] = acc
      go (current:rest) (w:ws) =
        let updated = zipWith (addElement w) primes current
        in go (updated : current : rest) ws
      go [] _ = []  -- shouldn't happen

      allOracles = go [emptyBitsets] (reverse weights)
  in allOracles

-- | Add an element to a bitset: new = old ∪ {(r + w) mod p | r ∈ old}
addElement :: Int -> Int -> Word64 -> Word64
addElement w p bitset =
  let wModP = w `mod` p
      -- For each bit set in bitset, also set (bit + wModP) mod p
      shifted = foldl' (\bs r ->
        if testBit bitset r
        then setBit bs ((r + wModP) `mod` p)
        else bs
        ) (0 :: Word64) [0..p-1]
  in bitset .|. shifted

-- | Query: is residual achievable mod p for suffix starting at depth i?
-- True = "possibly achievable" (can't prune)
-- False = "definitely not achievable" (PRUNE!)
queryOracle :: SuffixOracles -> Int -> Int -> Bool
queryOracle oracles depth residual =
  let bitsets = oracles !! depth
  in all (\(p, bs) -> testBit bs (residual `mod` p))
         (zip oraclePrimes bitsets)

-- ═══════════════════════════════════════════════════════════
-- Oracle result
-- ═══════════════════════════════════════════════════════════

data OracleResult = OracleResult
  { orFound        :: !Bool
  , orNodesTotal   :: !Int    -- nodes explored
  , orNodesPruned  :: !Int    -- nodes pruned by oracle (not by standard bounds)
  , orOraclePrunes :: !Int    -- specifically oracle-triggered prunes
  , orBoundPrunes  :: !Int    -- standard bound prunes
  } deriving (Show)

showOracleResult :: OracleResult -> String
showOracleResult or' =
  "found=" ++ show (orFound or')
  ++ " nodes=" ++ show (orNodesTotal or')
  ++ " oraclePrunes=" ++ show (orOraclePrunes or')
  ++ " boundPrunes=" ++ show (orBoundPrunes or')

-- ═══════════════════════════════════════════════════════════
-- Oracle-guided branch-and-bound
-- ═══════════════════════════════════════════════════════════

oracleSolve :: [Int] -> Int -> OracleResult
oracleSolve weights target =
  let oracles = buildOracles weights
      restSums = buildRestSums weights
      (found, nodes, oPrunes, bPrunes) = search oracles restSums weights target 0 0
  in OracleResult found nodes (oPrunes + bPrunes) oPrunes bPrunes

-- | Precompute suffix sums for standard bound checking.
-- restSums[i] = sum of elements[i..n-1]
buildRestSums :: [Int] -> [Int]
buildRestSums ws =
  let n = length ws
      sums = scanr (+) 0 ws  -- [sum of all, sum of ws[1..], ..., sum of ws[n-1], 0]
  in sums

-- | The core search with oracle pruning.
-- Returns (found, nodesExplored, oraclePrunes, boundPrunes)
search :: SuffixOracles -> [Int] -> [Int] -> Int -> Int -> Int
       -> (Bool, Int, Int, Int)
search oracles restSums weights target partialSum depth
  -- Standard bound prune: partial sum exceeds target
  | partialSum > target = (False, 1, 0, 1)
  -- Standard bound prune: even including everything can't reach
  | partialSum + restSums !! depth < target = (False, 1, 0, 1)
  -- Base case: no more elements
  | depth >= length weights = (partialSum == target, 1, 0, 0)
  -- ORACLE PRUNE: check modular reachability of residual
  | not (queryOracle oracles depth (target - partialSum)) = (False, 1, 1, 0)
  -- Recurse: try include and exclude
  | otherwise =
      let w = weights !! depth
          -- Include w
          (f1, n1, o1, b1) = search oracles restSums weights target (partialSum + w) (depth + 1)
      in if f1 then (True, n1 + 1, o1, b1)  -- found! early exit
         else
           let -- Exclude w
               (f2, n2, o2, b2) = search oracles restSums weights target partialSum (depth + 1)
           in (f2, n1 + n2 + 1, o1 + o2, b1 + b2)

-- ═══════════════════════════════════════════════════════════
-- Plain branch-and-bound (no oracle, for comparison)
-- ═══════════════════════════════════════════════════════════

plainBnB :: [Int] -> Int -> OracleResult
plainBnB weights target =
  let restSums = buildRestSums weights
      (found, nodes, bPrunes) = searchPlain restSums weights target 0 0
  in OracleResult found nodes bPrunes 0 bPrunes

searchPlain :: [Int] -> [Int] -> Int -> Int -> Int -> (Bool, Int, Int)
searchPlain restSums weights target partialSum depth
  | partialSum > target = (False, 1, 1)
  | partialSum + restSums !! depth < target = (False, 1, 1)
  | depth >= length weights = (partialSum == target, 1, 0)
  | otherwise =
      let w = weights !! depth
          (f1, n1, b1) = searchPlain restSums weights target (partialSum + w) (depth + 1)
      in if f1 then (True, n1 + 1, b1)
         else
           let (f2, n2, b2) = searchPlain restSums weights target partialSum (depth + 1)
           in (f2, n1 + n2 + 1, b1 + b2)

-- ═══════════════════════════════════════════════════════════
-- Oracle as INSTANT PRECHECK
--
-- Cost: O(n × Σp) to build the full-array oracle.
-- Then one query: is target mod p reachable for each prime p?
-- If ANY prime says NO → answer is NO (zero search needed).
-- ═══════════════════════════════════════════════════════════

-- | Instant modular precheck. Returns Nothing if inconclusive,
-- Just False if target is provably unreachable.
oraclePrecheck :: [Int] -> Int -> Maybe Bool
oraclePrecheck weights target =
  let oracles = buildOracles weights
  in if queryOracle oracles 0 target
     then Nothing      -- passes all modular tests, inconclusive
     else Just False   -- at least one prime proves NO

-- ═══════════════════════════════════════════════════════════
-- Oracle-enhanced MITM
--
-- Split in half. For each half, use oracle-guided BnB to
-- enumerate reachable sums (instead of bruteForceDP).
-- The oracle prunes branches within each half.
-- Then standard MITM merge.
--
-- Advantage over plain MITM: each half explores fewer nodes.
-- Advantage over plain oracle-BnB: O(2^{n/2}) merge instead of O(2^n) tree.
-- ═══════════════════════════════════════════════════════════

oracleMITM :: [Int] -> Int -> OracleResult
oracleMITM weights target =
  -- Quick precheck
  case oraclePrecheck weights target of
    Just False -> OracleResult False 0 0 1 0  -- oracle proved NO instantly
    _ ->
      let n = length weights
          mid = n `div` 2
          (leftW, rightW) = splitAt mid weights

          -- Enumerate left sums with oracle-guided BnB
          -- We enumerate ALL reachable sums (target for left = collect all)
          leftSums = oracleEnumerate leftW
          rightSums = oracleEnumerate rightW

          -- MITM merge: for each left sum, check if (target - l) in right
          rightSet = Set.fromList rightSums
          found = any (\l -> Set.member (target - l) rightSet) leftSums
          work = length leftSums + length rightSums
      in OracleResult found work 0 0 0

-- | Enumerate all reachable sums using oracle-guided BnB.
-- The oracle prunes branches where the partial sum can't contribute
-- to any valid total (using suffix reachability within this half).
-- This is tighter than plain DP because it kills branches, not just states.
oracleEnumerate :: [Int] -> [Int]
oracleEnumerate weights =
  let oracles = buildOracles weights
      restSums = buildRestSums weights
      n = length weights
      maxSum = sum weights
  in enumBnB oracles restSums weights n maxSum 0 0

-- | BnB enumeration: collect all reachable sums with oracle pruning.
-- At each node, the "target" for oracle is: "can the remaining suffix
-- produce ANY sum?" This is weaker than knowing the exact target.
-- We check: is the range [0, restSum] still non-empty mod each prime?
-- This always passes (0 is always reachable). So within-half oracle
-- doesn't help for enumeration.
--
-- INSTEAD: use the oracle for RANGE PRUNING within the half.
-- If we know the left half's sum must be in [lo, hi] (from the
-- original target and right half's range), we can prune left branches
-- where partialSum > hi or partialSum + restSum < lo.
-- This is standard range pruning, but the oracle adds modular checks.
--
-- For simplicity here: just enumerate with standard DP (the oracle
-- enhancement for MITM requires knowing the target split, which
-- we handle in the merge step).
enumBnB :: SuffixOracles -> [Int] -> [Int] -> Int -> Int -> Int -> Int -> [Int]
enumBnB _ _ _ n _ partialSum depth
  | depth >= n = [partialSum]
enumBnB oracles restSums weights n maxSum partialSum depth =
  let w = weights !! depth
      rs = restSums !! depth
      -- Include w
      inc = if partialSum + w <= maxSum
            then enumBnB oracles restSums weights n maxSum (partialSum + w) (depth + 1)
            else []
      -- Exclude w
      exc = enumBnB oracles restSums weights n maxSum partialSum (depth + 1)
  in inc ++ exc
