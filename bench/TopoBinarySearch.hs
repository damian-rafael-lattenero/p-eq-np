module Main where

{-
  TOPOLOGICAL BINARY SEARCH: shape the haystack to reveal the needle

  Instead of adding weights in arbitrary order, choose the order that
  maximally reduces the gap around T at each step. Like a sculptor
  shaping clay — each weight addition changes the topology, and we
  pick additions that make T's location most obvious.

  At step k:
    - Current reachable set R_k has a gap [lo, hi) containing T
    - For each unused weight w_i, adding it creates R_{k+1} = R_k ∪ (R_k + w_i)
    - The new gap around T might shrink (good!) or not (bad)
    - Pick the w_i that shrinks the gap most

  If the gap reaches 0: T is reachable (YES).
  If all weights are used and gap > 0: T is unreachable (NO).

  KEY QUESTION: how fast does the gap shrink?
    - If gap halves each step → O(log(gap₀)) = O(n) steps → POLYNOMIAL!
    - If gap shrinks by O(1) each step → O(gap₀) = O(2^n) → useless
    - If gap doesn't shrink → same as brute force

  But we DON'T need to build all of R_k (exponential). We only track
  the gap around T. At each step, we check: does adding w_i create
  any new sum in the current gap [lo, hi)?

  A new sum lands in [lo, hi) iff there exists s ∈ R_k such that
  lo ≤ s + w_i < hi, i.e., s ∈ [lo - w_i, hi - w_i).

  So: "does w_i shrink the gap?" = "does R_k contain any element in
  [lo - w_i, hi - w_i)?"

  If we track R_k as a sorted set, this is an O(log |R_k|) query.
  But |R_k| is still exponential...

  OPTIMIZATION: instead of tracking ALL of R_k, track only sums NEAR T.
  A window [T - W, T + W] where W = max weight. Sums outside this
  window can't possibly reach T in one more step.

  Experiment:
    1. FULL VERSION: track exact R_k, measure gap shrinkage per step
    2. GREEDY ORDERING: pick weight that minimally reduces gap vs random order
    3. WINDOW VERSION: track only sums within W of T (polynomial?)
    4. GAP CONVERGENCE: does the gap at T converge to 0 polynomially?
-}

import qualified Data.Set as Set
import qualified Data.IntSet as IS
import Data.List (foldl', sortBy, minimumBy, maximumBy)
import Data.Ord (comparing, Down(..))
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- | Find the gap containing T in a sorted set of sums
-- Returns (lo_neighbor, hi_neighbor) where lo < T < hi
-- If T is in the set, returns (T, T) with gap = 0
findGap :: IS.IntSet -> Int -> (Int, Int, Int)  -- (lo, hi, gap_size)
findGap sums target
  | IS.member target sums = (target, target, 0)
  | otherwise =
    let below = IS.lookupLE target sums
        above = IS.lookupGE target sums
    in case (below, above) of
         (Just lo, Just hi) -> (lo, hi, hi - lo)
         (Nothing, Just hi) -> (0, hi, hi)
         (Just lo, Nothing) -> (lo, lo + 1, 1)  -- shouldn't happen if T < sum_all
         _ -> (0, 0, 0)

-- | Add a weight to the reachable set
addWeight :: IS.IntSet -> Int -> IS.IntSet
addWeight sums w = IS.union sums (IS.map (+w) sums)

-- | Score a weight: how much does adding it shrink the gap at T?
-- Returns the new gap size after adding w
scoreWeight :: IS.IntSet -> Int -> Int -> Int
scoreWeight sums target w =
  let newSums = addWeight sums w
      (_, _, newGap) = findGap newSums target
  in newGap

-- | GREEDY topological binary search: at each step, pick the weight
-- that shrinks the gap at T the most.
-- Returns: [(step, weight_added, gap_before, gap_after)]
greedyTopoSearch :: [Int] -> Int -> [(Int, Int, Int, Int)]
greedyTopoSearch weights target =
  let n = length weights
      go sums unused step acc
        | IS.member target sums = acc  -- found!
        | null unused = acc            -- exhausted
        | otherwise =
            let (_, _, curGap) = findGap sums target
                -- Score each unused weight
                scored = [(i, scoreWeight sums target (weights !! i)) | i <- unused]
                -- Pick the one that minimizes new gap
                (bestIdx, bestGap) = minimumBy (comparing snd) scored
                bestW = weights !! bestIdx
                newSums = addWeight sums bestW
                newUnused = filter (/= bestIdx) unused
                entry = (step, bestW, curGap, bestGap)
            in go newSums newUnused (step + 1) (acc ++ [entry])
  in go (IS.singleton 0) [0..length weights - 1] 1 []

-- | RANDOM (natural) ordering for comparison
naturalOrderSearch :: [Int] -> Int -> [(Int, Int, Int, Int)]
naturalOrderSearch weights target =
  let go sums [] _ acc = acc
      go sums (w:ws) step acc
        | IS.member target sums = acc
        | otherwise =
            let (_, _, curGap) = findGap sums target
                newSums = addWeight sums w
                (_, _, newGap) = findGap newSums target
            in go newSums ws (step + 1) (acc ++ [(step, w, curGap, newGap)])
  in go (IS.singleton 0) weights 1 []

-- | WORST ordering: pick the weight that shrinks gap LEAST
worstOrderSearch :: [Int] -> Int -> [(Int, Int, Int, Int)]
worstOrderSearch weights target =
  let go sums unused step acc
        | IS.member target sums = acc
        | null unused = acc
        | otherwise =
            let (_, _, curGap) = findGap sums target
                scored = [(i, scoreWeight sums target (weights !! i)) | i <- unused]
                (worstIdx, worstGap) = maximumBy (comparing snd) scored
                worstW = weights !! worstIdx
                newSums = addWeight sums worstW
                newUnused = filter (/= worstIdx) unused
                entry = (step, worstW, curGap, worstGap)
            in go newSums newUnused (step + 1) (acc ++ [entry])
  in go (IS.singleton 0) [0..length weights - 1] 1 []

-- | WINDOW VERSION: only track sums within distance W of target
-- This is the polynomial approximation
windowSearch :: [Int] -> Int -> Int -> [(Int, Int, Int, Int)]
windowSearch weights target windowSize =
  let maxW = maximum weights
      go sums [] _ acc = acc
      go sums ((idx,w):rest) step acc
        | IS.member target sums = acc
        | otherwise =
            let (_, _, curGap) = findGap sums target
                newSums = addWeight sums w
                -- Prune: keep only sums within windowSize of target
                pruned = IS.filter (\s -> abs (s - target) <= windowSize) newSums
                -- Also keep 0 and small sums that might grow into range
                withBase = IS.union pruned (IS.filter (<= windowSize) newSums)
                (_, _, newGap) = findGap withBase target
            in go withBase rest (step + 1) (acc ++ [(step, w, curGap, newGap)])
      -- Sort weights: add those closest to T's "needs" first
      sorted = sortBy (comparing (\i -> abs (weights !! i - target `div` max 1 (length weights))))
                      [0..length weights - 1]
      indexed = [(i, weights !! i) | i <- sorted]
  in go (IS.singleton 0) indexed 1 []

mkHash :: Int -> ([Int], Int)
mkHash n =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
           | i <- [0..n-1 :: Int]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

mkHashYes :: Int -> ([Int], Int)
mkHashYes n = let (ws, _) = mkHash n in (ws, sum (take (n `div` 2) ws))

showF :: Int -> Double -> String
showF d x = let f = 10 ^ d :: Int
                r = fromIntegral (round (x * fromIntegral f) :: Int) / fromIntegral f :: Double
            in show r

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn " TOPOLOGICAL BINARY SEARCH: shape the haystack to find the needle"
  putStrLn " Choose weight order to maximally shrink the gap around T"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Gap trajectory — greedy vs natural vs worst
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. GAP TRAJECTORY: greedy vs natural ordering (YES, n=10) ==="
  putStrLn ""
  let (ws1, t1) = mkHashYes 10
  let greedy1 = greedyTopoSearch ws1 t1
      natural1 = naturalOrderSearch ws1 t1
  putStrLn "  Greedy (best weight first):"
  putStrLn $ "  " ++ padR 6 "step" ++ padR 12 "gap_before" ++ padR 12 "gap_after"
    ++ padR 12 "shrink%"
  mapM_ (\(s, _, gb, ga) -> do
    let shrink = if gb == 0 then 0
                 else (1 - fromIntegral ga / fromIntegral gb) * 100 :: Double
    putStrLn $ "  " ++ padR 6 (show s) ++ padR 12 (show gb) ++ padR 12 (show ga)
      ++ padR 12 (showF 1 shrink ++ "%")
    ) greedy1
  putStrLn ""
  putStrLn "  Natural (original order):"
  putStrLn $ "  " ++ padR 6 "step" ++ padR 12 "gap_before" ++ padR 12 "gap_after"
    ++ padR 12 "shrink%"
  mapM_ (\(s, _, gb, ga) -> do
    let shrink = if gb == 0 then 0
                 else (1 - fromIntegral ga / fromIntegral gb) * 100 :: Double
    putStrLn $ "  " ++ padR 6 (show s) ++ padR 12 (show gb) ++ padR 12 (show ga)
      ++ padR 12 (showF 1 shrink ++ "%")
    ) natural1
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Steps to close gap — scaling
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. STEPS TO CLOSE GAP: greedy vs natural vs worst ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 10 "greedy" ++ padR 10 "natural"
    ++ padR 10 "worst" ++ padR 8 "n"
  putStrLn (replicate 50 '-')
  mapM_ (\n -> do
    -- YES
    let (wsY, tY) = mkHashYes n
        gY = length (greedyTopoSearch wsY tY)
        nY = length (naturalOrderSearch wsY tY)
        wY = length (worstOrderSearch wsY tY)
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 10 (show gY)
      ++ padR 10 (show nY)
      ++ padR 10 (show wY)
      ++ padR 8 (show n)
    -- NO
    let (wsN, tN) = mkHash n
        gN = length (greedyTopoSearch wsN tN)
        nN = length (naturalOrderSearch wsN tN)
        wN = length (worstOrderSearch wsN tN)
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 10 (show gN)
      ++ padR 10 (show nN)
      ++ padR 10 (show wN)
      ++ padR 8 (show n)
    ) [6, 8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Gap halving rate — is it exponential shrinkage?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. GAP HALVING RATE: does gap shrink exponentially? ==="
  putStrLn "   (ratio = gap_after / gap_before; ratio < 1 = shrinking)"
  putStrLn ""
  let (ws3, t3) = mkHashYes 12
  let greedy3 = greedyTopoSearch ws3 t3
  putStrLn $ padR 6 "step" ++ padR 14 "gap_before" ++ padR 14 "gap_after"
    ++ padR 10 "ratio"
  putStrLn (replicate 44 '-')
  mapM_ (\(s, _, gb, ga) -> do
    let ratio = if gb == 0 then 0 else fromIntegral ga / fromIntegral gb :: Double
    putStrLn $ padR 6 (show s) ++ padR 14 (show gb) ++ padR 14 (show ga)
      ++ padR 10 (showF 4 ratio)
    ) greedy3
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: Window approximation — polynomial version
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. WINDOW VERSION: track only sums near T ==="
  putStrLn "   (polynomial memory if window = O(poly(n)))"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 10 "window" ++ padR 10 "steps"
    ++ padR 10 "found" ++ padR 10 "exact"
  putStrLn (replicate 52 '-')
  mapM_ (\n -> do
    let (wsY, tY) = mkHashYes n
        maxW = maximum wsY
        -- Window sizes: maxW, 2*maxW, n*maxW
        ws = [maxW, 2*maxW, n*maxW]
    mapM_ (\wSize -> do
      let trace = windowSearch wsY tY wSize
          steps = length trace
          found = case trace of
                    [] -> IS.member tY (IS.singleton 0)
                    _  -> let (_, _, _, lastGap) = last trace in lastGap == 0
          exactSteps = length (greedyTopoSearch wsY tY)
      putStrLn $ padR 5 (show n) ++ padR 6 "YES"
        ++ padR 10 (show wSize)
        ++ padR 10 (show steps)
        ++ padR 10 (show found)
        ++ padR 10 (show exactSteps)
      ) ws
    ) [6, 8, 10]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: The key metric — steps/n ratio
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. THE KEY METRIC: steps to gap=0 vs n ==="
  putStrLn "   steps = n → gap closed in linear time → POLYNOMIAL"
  putStrLn "   steps = n but |R_k| = 2^k → still exponential (in space)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "steps" ++ padR 10 "steps/n"
    ++ padR 12 "peak|R_k|" ++ padR 10 "2^n"
  putStrLn (replicate 48 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
        trace = greedyTopoSearch ws t
        steps = length trace
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show steps)
      ++ padR 10 (showF 1 (fromIntegral steps / fromIntegral n :: Double))
      ++ padR 12 (show ((2::Int)^steps))
      ++ padR 10 (show ((2::Int)^n))
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "ANALYSIS:"
  putStrLn " The gap at T shrinks with each weight added — that's guaranteed."
  putStrLn " Greedy ordering shrinks it FASTER than random."
  putStrLn " But: tracking R_k exactly requires O(2^k) space."
  putStrLn ""
  putStrLn " The dream: gap halves each step → O(n) steps, O(n) gap queries."
  putStrLn " The catch: each gap query needs R_k, which is exponential."
  putStrLn " The window version approximates R_k near T — does it suffice?"
  putStrLn ""
  putStrLn " If window works: we shaped the haystack with polynomial memory!"
  putStrLn " If not: the shape is visible but we can't afford to see it."
  putStrLn "═══════════════════════════════════════════════════════════════════"
