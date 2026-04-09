module PeqNP.StructuralSolver
  ( -- * Main solver (best: half-enum + on-the-fly + 4 complement matches)
    solve
  , SolveResult(..)
  , showSolveResult
  , MatchType(..)
    -- * Enriched types
  , PreNode(..)
  , Result(..)
  , enrichList
  , enrichTarget
  , meet
    -- * Enumerators
  , enumerateUnique
  , enumerateHalf
  , enumerateColumns
    -- * Utilities
  , complementElements
  , bitmaskToElements
    -- * Aliased solver (controlled aliasing, paper Section 7)
  , solveAliased
  , injectAliases
  , enumerateHalfAliased
    -- * Variant solvers
  , doubleMITM
  , DoubleMITMResult(..)
  , showDoubleMITMResult
  , aliasedDoubleMITM
  , doubleMITMv3
  ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.List (foldl', sort, sortBy)
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
-- ON-THE-FLY DOUBLE MITM v2
--
-- Paper: "Beyond Worst-Case Subset Sum" (2503.20162)
-- Half-enumeration + 4 complement match types + early exit
--
-- 1. Split into halves of size n/2
-- 2. Only enumerate subsets of size ≤ n/4 per half
-- 3. Complement trick: subset S with |S| > n/4 has complement
--    C = half \ S with |C| < n/4, sum(S) = halfTotal - sum(C)
-- 4. Four match types for target = leftPart + rightPart:
--      (s+s): sL + sR = target
--      (L+s): (leftTotal - sL) + sR = target
--      (s+L): sL + (rightTotal - sR) = target
--      (L+L): (leftTotal - sL) + (rightTotal - sR) = target
-- 5. On-the-fly: check matches WHILE building right side
--    → early exit on first match (huge win for YES instances)
--
-- Work per half: O(Σ_{k≤n/4} C(n/2,k)) ≈ O(2^{n/2} / √n)
-- Match check: O(1) per new sum (IntMap lookup)
-- ═══════════════════════════════════════════════════════════

data MatchType = SmallSmall | LargeSmall | SmallLarge | LargeLarge
  deriving (Show, Eq)

data SolveResult = SolveResult
  { solFound     :: !Bool
  , solSolution  :: !(Maybe [Int])
  , solMatchType :: !(Maybe MatchType)
  , solLeftU     :: !Int       -- unique sums in left half
  , solRightU    :: !Int       -- unique sums in right half (at exit)
  , solWorkDone  :: !Int       -- matching checks before solution found
  , solTotalEnum :: !Int       -- total entries enumerated (left + right at exit)
  } deriving (Show)

showSolveResult :: SolveResult -> String
showSolveResult m =
  "found=" ++ show (solFound m)
  ++ " match=" ++ maybe "none" show (solMatchType m)
  ++ " leftU=" ++ show (solLeftU m)
  ++ " rightU=" ++ show (solRightU m)
  ++ " work=" ++ show (solWorkDone m) ++ "/" ++ show (solTotalEnum m)
  ++ case solSolution m of
       Just sol -> " solution=" ++ show sol
       Nothing  -> ""

-- | Half-enumeration: only enumerate subsets of size ≤ maxSize.
-- Produces at most Σ_{k=0}^{maxSize} C(n,k) unique sums.
-- Optimized: fold-based insertion eliminates intermediate list/map allocation.
enumerateHalf :: Int -> [Int] -> PreNode
enumerateHalf maxSize weights =
  let initial :: IM.IntMap Int
      initial = IM.singleton 0 0
      step :: IM.IntMap Int -> (Int, Int) -> IM.IntMap Int
      step memo (idx, w) =
        let bit = setBit 0 idx
        in IM.foldlWithKey' (\acc s mask ->
             if popCount mask < maxSize
             then IM.insertWith (\_ old -> old) (s + w) (mask .|. bit) acc
             else acc
           ) memo memo
      final = foldl' step initial (zip [0..] weights)
  in PreNode { pnSums = final, pnUniqueCount = IM.size final, pnElements = weights }

-- | Half-enumeration with controlled aliasing.
-- Injects δ duplicates: during sum computation, aliased elements
-- contribute their alias's value, forcing collisions.
-- The bitmask tracks ORIGINAL indices for correct reconstruction.
-- Returns (PreNode with aliased sums, original weights for verification).
enumerateHalfAliased :: Int -> Int -> [Int] -> PreNode
enumerateHalfAliased maxSize delta weights =
  let aliased = injectAliases delta weights
      initial :: IM.IntMap Int
      initial = IM.singleton 0 0
      step :: IM.IntMap Int -> (Int, Int) -> IM.IntMap Int
      step memo (idx, w) =
        let bit = setBit 0 idx
        in IM.foldlWithKey' (\acc s mask ->
             if popCount mask < maxSize
             then IM.insertWith (\_ old -> old) (s + w) (mask .|. bit) acc
             else acc
           ) memo memo
      final = foldl' step initial (zip [0..] aliased)
  in PreNode { pnSums = final, pnUniqueCount = IM.size final, pnElements = weights }

-- | Inject δ aliases: replace δ elements with copies of their nearest neighbor.
-- Each alias forces one collision, reducing U by ~25% per alias (factor 0.75^δ).
-- Paper Section 7: guaranteed O*(2^{n/2 - 0.415·δ}).
injectAliases :: Int -> [Int] -> [Int]
injectAliases 0 ws = ws
injectAliases _ [] = []
injectAliases _ [x] = [x]
injectAliases delta ws =
  let indexed = zip [0 :: Int ..] ws
      sorted = sortBy (\(_,a) (_,b) -> compare a b) indexed
      -- Find δ closest pairs by value
      diffs = zipWith (\(i1,v1) (i2,v2) -> (v2-v1, i1, i2))
                sorted (drop 1 sorted)
      bestPairs = take delta (sortBy (\(d,_,_) (e,_,_) -> compare d e) diffs)
      -- Build replacement map: victim → replacement value
      repMap = IM.fromList [(j, ws !! i) | (_d, i, j) <- bestPairs]
  in [IM.findWithDefault w idx repMap | (idx, w) <- zip [0..] ws]

-- | On-the-fly double MITM with half-enumeration and 4 match types.
-- Enumerates left side fully (size ≤ n/4), then builds right side
-- incrementally, checking for matches after each element addition.
-- Early-exits on first match found.
solve :: [Int] -> Int -> SolveResult
solve weights target =
  let n = length weights
      mid = n `div` 2
      (leftW, rightW) = splitAt mid weights
      leftTotal  = sum leftW
      rightTotal = sum rightW
      halfSize   = max 1 (n `div` 4)

      -- Step 1: Build left side fully (subsets of size ≤ halfSize)
      leftNode = enumerateHalf halfSize leftW
      leftSums = pnSums leftNode
      leftU    = pnUniqueCount leftNode

      -- Check 4 match types for a given right sum sR.
      -- Returns (matchType, leftSum used as key in leftSums).
      check :: Int -> Maybe (MatchType, Int)
      check sR =
        let t1 = target - sR
            t2 = leftTotal + sR - target
            t3 = target + sR - rightTotal
            t4 = leftTotal + rightTotal - target - sR
        in  if t1 >= 0 && IM.member t1 leftSums then Just (SmallSmall, t1)
            else if t2 >= 0 && IM.member t2 leftSums then Just (LargeSmall, t2)
            else if t3 >= 0 && IM.member t3 leftSums then Just (SmallLarge, t3)
            else if t4 >= 0 && IM.member t4 leftSums then Just (LargeLarge, t4)
            else Nothing

      -- Step 2: On-the-fly right enumeration with matching.
      -- For each right element, fold over rMap to extend+check in one pass.
      -- No intermediate list allocation.
      go :: IM.IntMap Int -> [(Int, Int)] -> Int
         -> (Maybe (MatchType, Int, Int, Int), Int, Int)
      go rMap [] work = (Nothing, work, IM.size rMap)
      go rMap ((idx, w):rest) work =
        let bit = setBit 0 idx
            -- Single fold: extend valid entries, check new sums, merge
            (merged, matched, work') = IM.foldlWithKey'
              (\(acc, hit, wk) s mask ->
                if popCount mask >= halfSize then (acc, hit, wk)
                else let sR   = s + w
                         rMask = mask .|. bit
                     in case hit of
                          Just _ -> -- already found match, just merge
                            (IM.insertWith (\_ old -> old) sR rMask acc, hit, wk)
                          Nothing ->
                            if IM.member sR acc
                            then (acc, Nothing, wk + 1)  -- already known sum
                            else let acc' = IM.insert sR rMask acc
                                 in case check sR of
                                      Just (mt, sL) -> (acc', Just (mt, sL, sR, rMask), wk + 1)
                                      Nothing       -> (acc', Nothing, wk + 1)
              ) (rMap, Nothing, work) rMap
        in case matched of
             Just hit -> (Just hit, work', IM.size merged)
             Nothing  -> go merged rest work'

      -- Check empty right subset first (sR = 0)
      (matchResult, workDone, rightU) = case check 0 of
        Just (mt, sL) -> (Just (mt, sL, 0, 0), 0, 1)
        Nothing       -> go (IM.singleton 0 0) (zip [0..] rightW) 0

      -- Reconstruct solution from match
      solution = case matchResult of
        Nothing -> Nothing
        Just (mt, sL, sR, rMask) ->
          let lMask = leftSums IM.! sL
              lElems = case mt of
                SmallSmall -> bitmaskToElements leftW lMask
                SmallLarge -> bitmaskToElements leftW lMask
                LargeSmall -> complementElements leftW lMask
                LargeLarge -> complementElements leftW lMask
              rElems = case mt of
                SmallSmall -> bitmaskToElements rightW rMask
                LargeSmall -> bitmaskToElements rightW rMask
                SmallLarge -> complementElements rightW rMask
                LargeLarge -> complementElements rightW rMask
              combined = lElems ++ rElems
          in if sum combined == target then Just combined else Nothing

      matchType = case matchResult of
        Just (mt, _, _, _) -> Just mt
        _                  -> Nothing

  in SolveResult
    { solFound     = case solution of { Just _ -> True; Nothing -> False }
    , solSolution  = solution
    , solMatchType = matchType
    , solLeftU     = leftU
    , solRightU    = rightU
    , solWorkDone  = workDone
    , solTotalEnum = leftU + rightU
    }

-- | Solve with controlled aliasing (paper Section 7).
-- Aliasing injects δ duplicates per half: during enumeration, aliased
-- elements contribute their alias's value, forcing collisions and
-- reducing U by ~0.75^δ.  Bitmasks track ORIGINAL indices.
--
-- Flow: enumerate with aliased weights → match using aliased totals →
-- verify each hit with original weights (reject false positives) →
-- if no verified match, fall back to complete (unaliased) solve.
--
-- Incomplete: aliased solver can miss solutions that rely on an aliased
-- element's true value.  Fallback guarantees correctness.
solveAliased :: Int -> [Int] -> Int -> SolveResult
solveAliased delta weights target
  | delta <= 0 = solve weights target
  | otherwise  =
    let n = length weights
        mid = n `div` 2
        (leftW, rightW) = splitAt mid weights
        halfSize = max 1 (n `div` 4)

        -- Aliased weights for sum computation
        leftA  = injectAliases delta leftW
        rightA = injectAliases delta rightW
        leftTotalA  = sum leftA
        rightTotalA = sum rightA

        -- Step 1: Build left with ALIASED weights (fewer unique sums)
        leftNode = enumerateHalf halfSize leftA
        leftSums = pnSums leftNode
        leftU    = pnUniqueCount leftNode

        -- Match check using ALIASED totals
        check :: Int -> Maybe (MatchType, Int)
        check sR =
          let t1 = target - sR
              t2 = leftTotalA + sR - target
              t3 = target + sR - rightTotalA
              t4 = leftTotalA + rightTotalA - target - sR
          in  if t1 >= 0 && IM.member t1 leftSums then Just (SmallSmall, t1)
              else if t2 >= 0 && IM.member t2 leftSums then Just (LargeSmall, t2)
              else if t3 >= 0 && IM.member t3 leftSums then Just (SmallLarge, t3)
              else if t4 >= 0 && IM.member t4 leftSums then Just (LargeLarge, t4)
              else Nothing

        -- Verify a match using ORIGINAL weights. Returns Nothing on false positive.
        verify :: MatchType -> Int -> Int -> Maybe [Int]
        verify mt sL rMask =
          let lMask = leftSums IM.! sL
              lElems = case mt of
                SmallSmall -> bitmaskToElements leftW lMask
                SmallLarge -> bitmaskToElements leftW lMask
                LargeSmall -> complementElements leftW lMask
                LargeLarge -> complementElements leftW lMask
              rElems = case mt of
                SmallSmall -> bitmaskToElements rightW rMask
                LargeSmall -> bitmaskToElements rightW rMask
                SmallLarge -> complementElements rightW rMask
                LargeLarge -> complementElements rightW rMask
              combined = lElems ++ rElems
          in if sum combined == target then Just combined else Nothing

        -- Step 2: On-the-fly right enumeration with ALIASED weights.
        -- Match+verify in one pass.  DON'T early-exit on unverified matches.
        go :: IM.IntMap Int -> [(Int, Int)] -> Int
           -> (Maybe (MatchType, [Int]), Int, Int)
        go rMap [] work = (Nothing, work, IM.size rMap)
        go rMap ((idx, w):rest) work =
          let bit = setBit 0 idx
              (merged, found, work') = IM.foldlWithKey'
                (\(acc, hit, wk) s mask ->
                  case hit of
                    Just _ -> (IM.insertWith (\_ o -> o) (s+w) (mask .|. bit) acc, hit, wk)
                    Nothing ->
                      if popCount mask >= halfSize then (acc, Nothing, wk)
                      else let sR = s + w; rMask = mask .|. bit
                           in if IM.member sR acc then (acc, Nothing, wk+1)
                              else let acc' = IM.insert sR rMask acc
                                   in case check sR of
                                        Just (mt, sL) ->
                                          case verify mt sL rMask of
                                            Just sol -> (acc', Just (mt, sol), wk+1)
                                            Nothing  -> (acc', Nothing, wk+1) -- false positive
                                        Nothing -> (acc', Nothing, wk+1)
                ) (rMap, Nothing, work) rMap
          in case found of
               Just hit -> (Just hit, work', IM.size merged)
               Nothing  -> go merged rest work'

        -- Check empty right subset
        (aliasedResult, workDone, rightU) = case check 0 of
          Just (mt, sL) -> case verify mt sL 0 of
            Just sol -> (Just (mt, sol), 0, 1)
            Nothing  -> go (IM.singleton 0 0) (zip [0..] rightA) 0
          Nothing -> go (IM.singleton 0 0) (zip [0..] rightA) 0

    in case aliasedResult of
         Just (mt, sol) -> SolveResult
           { solFound = True, solSolution = Just sol, solMatchType = Just mt
           , solLeftU = leftU, solRightU = rightU
           , solWorkDone = workDone, solTotalEnum = leftU + rightU }
         Nothing ->
           -- Aliased pass found nothing → fall back to complete solver
           let complete = solve weights target
           in complete { solLeftU = leftU  -- report aliased U for comparison
                       }

-- ═══════════════════════════════════════════════════════════
-- COLUMN-BY-COLUMN DOUBLE MITM v3
--
-- Paper: Section 5-6. Enumerates k-subsets by increasing
-- cardinality. At column k, extends ALL k-subsets in the
-- frontier by EVERY unused element. Collision detection via
-- memo table (sum → canonical bitmask).
--
-- Key difference from v2 (element-by-element):
--   v2: process element 0, then 1, etc. After element i,
--       have all subsets of {0..i}.
--   v3: process column 0 (singletons), then 1 (pairs), etc.
--       After column k, have all subsets of size ≤ k+1 from
--       ALL elements.
--
-- Pruning: if a (k+1)-subset's sum already exists in memo,
-- it is NOT added to the next frontier. Only truly new sums
-- propagate. The paper proves this is complete (Theorem 6).
--
-- Advantage: small subsets explored first. Solutions using
-- few elements from one side are found earliest.
--
-- Complexity: O*(U · n²) deterministic per half
-- ═══════════════════════════════════════════════════════════

-- | State for column-by-column enumeration.
-- Frontier = entries from the last column that produced NEW unique sums.
data ColEnum = ColEnum
  { ceMemo     :: !(IM.IntMap Int)  -- sum → canonical bitmask (all discovered)
  , ceFrontier :: ![(Int, Int)]     -- frontier: [(sum, bitmask)] for next expansion
  }

-- | Expand one column: generate (k+1)-subsets from frontier k-subsets.
-- For each frontier entry, try adding each element not in its bitmask.
-- Dedup candidates, merge with memo. New sums → next frontier.
-- Returns updated state and list of newly discovered (sum, mask) pairs.
colExpand :: Int -> [Int] -> ColEnum -> (ColEnum, [(Int, Int)])
colExpand nElems weights (ColEnum memo frontier) =
  let -- Generate all candidate (k+1)-subsets
      candidates = [ (s + weights !! idx, mask .|. setBit 0 idx)
                   | (s, mask) <- frontier
                   , idx <- [0..nElems - 1]
                   , not (testBit mask idx)
                   ]
      -- Deduplicate candidates: keep lex-smallest bitmask per sum
      candMap = foldl' (\m (s, mask) ->
        IM.insertWith (\new old -> min new old) s mask m
        ) IM.empty candidates
      -- Merge with memo: new sums → frontier, updates → just fix canonical
      (memo', nextFrontier) = IM.foldlWithKey' (\(m, nf) s mask ->
        case IM.lookup s m of
          Nothing -> (IM.insert s mask m, (s, mask) : nf)
          Just ex | mask < ex -> (IM.insert s mask m, nf)
                  | otherwise -> (m, nf)
        ) (memo, []) candMap
  in (ColEnum memo' nextFrontier, nextFrontier)

-- | Enumerate all unique sums column-by-column up to subset size maxK.
-- After maxK columns, the memo contains all unique sums reachable
-- by subsets of size 0 through maxK.
enumerateColumns :: Int -> [Int] -> PreNode
enumerateColumns maxK weights =
  let nElems = length weights
      go ce k
        | k >= maxK = ce
        | null (ceFrontier ce) = ce  -- no more new sums to expand
        | otherwise = let (ce', _) = colExpand nElems weights ce
                      in go ce' (k + 1)
      initial = ColEnum (IM.singleton 0 0) [(0, 0)]
      final = go initial 0
  in PreNode
    { pnSums = ceMemo final
    , pnUniqueCount = IM.size (ceMemo final)
    , pnElements = weights
    }

-- | Column-by-column double MITM with on-the-fly matching (paper's Sec 6).
-- Builds left side fully via column enumeration, then expands right side
-- column by column, checking for matches after each column.
-- Early-exits on first match found.
doubleMITMv3 :: [Int] -> Int -> SolveResult
doubleMITMv3 weights target =
  let n = length weights
      mid = n `div` 2
      (leftW, rightW) = splitAt mid weights
      leftTotal  = sum leftW
      rightTotal = sum rightW
      maxK = max 1 (n `div` 4)
      nR = length rightW

      -- Build left side fully (column-by-column)
      leftNode = enumerateColumns maxK leftW
      leftSums = pnSums leftNode
      leftU    = pnUniqueCount leftNode

      -- 4 complement match types (same as v2)
      check :: Int -> Maybe (MatchType, Int)
      check sR =
        let t1 = target - sR
            t2 = leftTotal + sR - target
            t3 = target + sR - rightTotal
            t4 = leftTotal + rightTotal - target - sR
        in  if t1 >= 0 && IM.member t1 leftSums then Just (SmallSmall, t1)
            else if t2 >= 0 && IM.member t2 leftSums then Just (LargeSmall, t2)
            else if t3 >= 0 && IM.member t3 leftSums then Just (SmallLarge, t3)
            else if t4 >= 0 && IM.member t4 leftSums then Just (LargeLarge, t4)
            else Nothing

      -- Right side: expand column by column, check new sums each time
      goCol :: ColEnum -> Int -> Int
            -> (Maybe (MatchType, Int, Int, Int), Int, Int)
      goCol ce k work
        | k >= maxK = (Nothing, work, IM.size (ceMemo ce))
        | null (ceFrontier ce) = (Nothing, work, IM.size (ceMemo ce))
        | otherwise =
            let (ce', newSums) = colExpand nR rightW ce
                (matched, work') = checkNewSums newSums work
            in case matched of
                 Just hit -> (Just hit, work', IM.size (ceMemo ce'))
                 Nothing  -> goCol ce' (k + 1) work'

      checkNewSums :: [(Int, Int)] -> Int
                   -> (Maybe (MatchType, Int, Int, Int), Int)
      checkNewSums [] w = (Nothing, w)
      checkNewSums ((sR, rMask):rest) w =
        case check sR of
          Just (mt, sL) -> (Just (mt, sL, sR, rMask), w + 1)
          Nothing       -> checkNewSums rest (w + 1)

      -- Check empty right subset (sR = 0) before column expansion
      initialCE = ColEnum (IM.singleton 0 0) [(0, 0)]
      (matchResult, workDone, rightU) = case check 0 of
        Just (mt, sL) -> (Just (mt, sL, 0, 0), 0, 1)
        Nothing       -> goCol initialCE 0 0

      -- Reconstruct solution (same as v2)
      solution = case matchResult of
        Nothing -> Nothing
        Just (mt, sL, _sR, rMask) ->
          let lMask = leftSums IM.! sL
              lElems = case mt of
                SmallSmall -> bitmaskToElements leftW lMask
                SmallLarge -> bitmaskToElements leftW lMask
                LargeSmall -> complementElements leftW lMask
                LargeLarge -> complementElements leftW lMask
              rElems = case mt of
                SmallSmall -> bitmaskToElements rightW rMask
                LargeSmall -> bitmaskToElements rightW rMask
                SmallLarge -> complementElements rightW rMask
                LargeLarge -> complementElements rightW rMask
              combined = lElems ++ rElems
          in if sum combined == target then Just combined else Nothing

      matchType = case matchResult of
        Just (mt, _, _, _) -> Just mt
        _                  -> Nothing

  in SolveResult
    { solFound     = case solution of { Just _ -> True; Nothing -> False }
    , solSolution  = solution
    , solMatchType = matchType
    , solLeftU     = leftU
    , solRightU    = rightU
    , solWorkDone  = workDone
    , solTotalEnum = leftU + rightU
    }

-- ═══════════════════════════════════════════════════════════
-- Utilities
-- ═══════════════════════════════════════════════════════════

bitmaskToElements :: [Int] -> Int -> [Int]
bitmaskToElements ws mask =
  [w | (i, w) <- zip [0..] ws, testBit mask i]

complementElements :: [Int] -> Int -> [Int]
complementElements ws mask =
  [w | (i, w) <- zip [0..] ws, not (testBit mask i)]
