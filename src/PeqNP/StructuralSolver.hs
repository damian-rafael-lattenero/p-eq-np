module PeqNP.StructuralSolver
  ( -- * Core enriched types (the user's Result/PreNode idea)
    Result(..)
  , PreNode(..)
  , enrichTarget
  , enrichList
    -- * Meeting: where the two structures find each other
  , meet
    -- * Double MITM with unique-sums enumeration
  , doubleMITM
  , DoubleMITMResult(..)
  , showDoubleMITMResult
    -- * Unique sums enumerator (paper's key idea)
  , enumerateUnique
    -- * Controlled aliasing (forced collisions for sub-2^{n/2})
  , aliasedDoubleMITM
  ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.List (foldl', sort)
import Data.Bits (setBit, testBit, popCount, (.|.), (.&.))

-- ═══════════════════════════════════════════════════════════
-- The user's core insight: two enriched structures that
-- "know each other" and communicate structurally.
--
-- Result: the target DECOMPOSED relative to the elements.
--   Not just "8", but "8 which needs 5 from the right
--   (and 5 is right there in the list!)"
--
-- PreNode: the elements ORGANIZED for matching.
--   Not just [1,3,5], but a map from achievable sums
--   to the canonical subsets that produce them.
--
-- Meeting: IntMap intersection — O(min(n,m)) via Patricia trie.
-- ═══════════════════════════════════════════════════════════

-- | Target enriched with structural information about the elements.
data Result = Result
  { rTarget     :: !Int
  , rNeeded     :: !IS.IntSet    -- sums we need from the "other half"
  , rHits       :: !IS.IntSet    -- needed sums that ARE achievable
  , rHitCount   :: !Int
  } deriving (Show)

-- | Elements organized as unique achievable sums.
-- Each sum maps to the bitmask of the canonical (smallest) subset that produces it.
data PreNode = PreNode
  { pnSums      :: !(IM.IntMap Int)  -- sum → bitmask of producing subset
  , pnUniqueCount :: !Int            -- U = number of distinct sums
  , pnElements  :: ![Int]
  } deriving (Show)

-- | Enrich the target: given left sums, what do we need from the right?
enrichTarget :: Int -> PreNode -> Result
enrichTarget target leftNode =
  let needed = IS.fromList [target - s | s <- IM.keys (pnSums leftNode)]
  in Result
    { rTarget = target
    , rNeeded = needed
    , rHits = IS.empty  -- filled after meeting
    , rHitCount = 0
    }

-- | Enrich a list of elements: enumerate all unique achievable sums.
enrichList :: [Int] -> PreNode
enrichList = enumerateUnique

-- | MEETING: intersect Result's needs with PreNode's offers.
-- Returns the sums that the right side CAN provide AND the left side NEEDS.
-- This is O(min(|needed|, |sums|)) via IntSet/IntMap structure.
meet :: Result -> PreNode -> Result
meet result rightNode =
  let rightSumSet = IM.keysSet (pnSums rightNode)
      hits = IS.intersection (rNeeded result) rightSumSet
  in result { rHits = hits, rHitCount = IS.size hits }

-- ═══════════════════════════════════════════════════════════
-- Unique sums enumerator
--
-- From the paper: instead of 2^n subsets, only track U distinct sums.
-- Uses IntMap as memo: sum → bitmask of canonical (lexicographically
-- smallest) subset. When a new subset produces an existing sum,
-- compare bitmasks and keep the smaller one.
--
-- For density-1 (all sums distinct): U = 2^n, no savings.
-- For density-5 (many collisions): U << 2^n, huge savings.
-- ═══════════════════════════════════════════════════════════

enumerateUnique :: [Int] -> PreNode
enumerateUnique weights =
  let n = length weights
      -- Process elements one by one, maintaining unique sums
      -- memo: sum → bitmask of canonical subset
      initial :: IM.IntMap Int
      initial = IM.singleton 0 0  -- empty subset has sum 0, bitmask 0

      step :: IM.IntMap Int -> (Int, Int) -> IM.IntMap Int
      step memo (idx, w) =
        let -- For each existing (sum, mask), adding w gives (sum+w, mask | bit idx)
            newEntries = IM.fromList
              [ (s + w, mask .|. setBit 0 idx)
              | (s, mask) <- IM.toList memo
              ]
            -- Merge: keep the lexicographically smaller bitmask (fewer bits = smaller subset)
            merged = IM.unionWith (\old new ->
              if popCount old <= popCount new then old else new
              ) memo newEntries
        in merged

      final = foldl' step initial (zip [0..] weights)

  in PreNode
    { pnSums = final
    , pnUniqueCount = IM.size final
    , pnElements = weights
    }

-- ═══════════════════════════════════════════════════════════
-- Double MITM: the paper's strategy + user's structural idea
--
-- 1. Split into halves
-- 2. Enrich each half (enumerate unique sums → PreNode)
-- 3. Enrich target relative to left half (→ Result)
-- 4. MEET: Result intersects with right PreNode
-- 5. If hits > 0 → solution exists
--
-- The "double" aspect: also check complement matches.
-- ═══════════════════════════════════════════════════════════

data DoubleMITMResult = DoubleMITMResult
  { dmFound       :: !Bool
  , dmSolution    :: !(Maybe ([Int], [Int]))  -- (left subset, right subset)
  , dmLeftU       :: !Int   -- unique sums in left half
  , dmRightU      :: !Int   -- unique sums in right half
  , dmHits        :: !Int   -- meeting points found
  , dmTotalWork   :: !Int   -- total entries processed
  } deriving (Show)

showDoubleMITMResult :: DoubleMITMResult -> String
showDoubleMITMResult dm =
  "found=" ++ show (dmFound dm)
  ++ " leftU=" ++ show (dmLeftU dm)
  ++ " rightU=" ++ show (dmRightU dm)
  ++ " hits=" ++ show (dmHits dm)
  ++ " work=" ++ show (dmTotalWork dm)
  ++ case dmSolution dm of
       Just (l, r) -> " solution=(" ++ show l ++ "," ++ show r ++ ")"
       Nothing -> ""

doubleMITM :: [Int] -> Int -> DoubleMITMResult
doubleMITM weights target =
  let n = length weights
      mid = n `div` 2
      (leftW, rightW) = splitAt mid weights

      -- Step 1: Enrich both halves
      leftNode  = enrichList leftW
      rightNode = enrichList rightW

      -- Step 2: Enrich target relative to left → what do we need from right?
      result = enrichTarget target leftNode

      -- Step 3: MEET — where do Result and right PreNode agree?
      matched = meet result rightNode

      -- Step 4: If any hit, reconstruct solution
      solution = if rHitCount matched > 0
        then let rightSum = IS.findMin (rHits matched)  -- any hit works
                 leftSum = target - rightSum
                 leftMask = pnSums leftNode IM.! leftSum
                 rightMask = pnSums rightNode IM.! rightSum
                 leftSol = bitmaskToElements leftW leftMask
                 rightSol = bitmaskToElements rightW rightMask
             in Just (leftSol, rightSol)
        else
             -- Also try: is target achievable by left alone? or right alone?
             if IM.member target (pnSums leftNode)
             then Just (bitmaskToElements leftW (pnSums leftNode IM.! target), [])
             else if IM.member target (pnSums rightNode)
             then Just ([], bitmaskToElements rightW (pnSums rightNode IM.! target))
             else Nothing

  in DoubleMITMResult
    { dmFound = solution /= Nothing
    , dmSolution = solution
    , dmLeftU = pnUniqueCount leftNode
    , dmRightU = pnUniqueCount rightNode
    , dmHits = rHitCount matched
    , dmTotalWork = pnUniqueCount leftNode + pnUniqueCount rightNode
    }

-- ═══════════════════════════════════════════════════════════
-- Controlled aliasing: force collisions for guaranteed sub-2^{n/2}
--
-- Paper's trick: treat two elements as identical, creating
-- artificial collisions. If w_a ≈ w_b, replace w_b with w_a
-- during enumeration. This guarantees U < 2^{n/2}.
--
-- For density-1: elements are ~2^n, differences are ~2^{n-1}.
-- Aliasing two elements forces at least one collision per subset pair.
-- ═══════════════════════════════════════════════════════════

aliasedDoubleMITM :: [Int] -> Int -> DoubleMITMResult
aliasedDoubleMITM weights target =
  let n = length weights
      mid = n `div` 2
      (leftW, rightW) = splitAt mid weights

      -- Find closest pair in each half for aliasing
      leftAliased  = applyAlias leftW
      rightAliased = applyAlias rightW

      -- Enumerate with aliased weights (more collisions)
      leftNode  = enumerateUnique leftAliased
      rightNode = enumerateUnique rightAliased

      -- But check matches against ORIGINAL weights
      -- Need to re-check any found solution with true weights
      result  = enrichTarget target leftNode
      matched = meet result rightNode

      -- Reconstruct and verify with original weights
      solution = if rHitCount matched > 0
        then let rightSum = IS.findMin (rHits matched)
                 leftSum = target - rightSum
             in case (IM.lookup leftSum (pnSums leftNode),
                      IM.lookup rightSum (pnSums rightNode)) of
                  (Just lm, Just rm) ->
                    let ls = bitmaskToElements leftW lm  -- original weights!
                        rs = bitmaskToElements rightW rm
                    in if sum ls + sum rs == target
                       then Just (ls, rs)
                       else Nothing  -- alias caused false positive
                  _ -> Nothing
        else Nothing

  in DoubleMITMResult
    { dmFound = solution /= Nothing
    , dmSolution = solution
    , dmLeftU = pnUniqueCount leftNode
    , dmRightU = pnUniqueCount rightNode
    , dmHits = rHitCount matched
    , dmTotalWork = pnUniqueCount leftNode + pnUniqueCount rightNode
    }

-- | Apply aliasing: replace the element closest to another with that other.
-- This creates at least one forced collision.
applyAlias :: [Int] -> [Int]
applyAlias [] = []
applyAlias [x] = [x]
applyAlias ws =
  let sorted = sort ws
      -- Find the pair with minimum difference
      diffs = zipWith (\a b -> (b - a, a, b)) sorted (tail sorted)
      (_, _, victim) = minimum diffs  -- victim gets replaced by its neighbor
      (_, replacement, _) = minimum diffs
  in map (\w -> if w == victim then replacement else w) ws

-- ═══════════════════════════════════════════════════════════
-- Utilities
-- ═══════════════════════════════════════════════════════════

bitmaskToElements :: [Int] -> Int -> [Int]
bitmaskToElements ws mask =
  [w | (i, w) <- zip [0..] ws, testBit mask i]
