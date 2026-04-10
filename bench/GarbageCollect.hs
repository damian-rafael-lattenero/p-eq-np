module Main where

{-
  THE "GARBAGE COLLECTOR" APPROACH TO SUBSET SUM

  Analogy: like Rust's ownership model or a GC, track which partial sums
  are still "alive" (can possibly lead to T) and drop the rest immediately.

  DP step k: we've processed weights w_1..w_k.
  Live set = {subset sums that can still reach T with remaining weights}.

  GC rule (tightest possible bound-based pruning):
    After step k, sum s is ALIVE iff:
      s ≤ T  AND  s + remaining ≥ T
    where remaining = Σ w_{k+1}..w_n

    Drop everything outside the window [T - remaining, T].

  Three experiments:
    1. BOUND-GC: prune with bounds at every step, measure peak live set
    2. BUDGET-CAP: hard cap at B sums (keep closest to T), measure accuracy
    3. COMPARISON: peak live set vs 2^n — polynomial or exponential?

  If peak live set = O(poly(n)) → polynomial algorithm discovered
  If peak live set = O(2^n) → GC can't tame the beast
-}

import qualified Data.IntSet as IS
import Data.List (foldl', sortBy)
import Data.Ord (comparing, Down(..))
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- | One step of DP: add weight w to all existing sums
dpStep :: Int -> IS.IntSet -> IS.IntSet
dpStep w sums = IS.union sums (IS.map (+w) sums)

-- | GC: remove sums outside the feasible window [lo, hi]
-- s is alive iff s ≤ T AND s + remaining ≥ T
-- i.e. T - remaining ≤ s ≤ T
gcPrune :: Int -> Int -> IS.IntSet -> IS.IntSet
gcPrune target remaining sums =
  let lo = max 0 (target - remaining)
      hi = target
  in IS.filter (\s -> s >= lo && s <= hi) sums

-- | Full DP with GC at every step. Returns: per-step live set sizes + final result.
dpWithGC :: [Int] -> Int -> ([Int], Bool)
dpWithGC weights target =
  let suffixSums = tail $ scanr (+) 0 weights  -- remaining after each step
      (finalSet, sizes) = foldl' (\(sums, szs) (w, rem') ->
        let sums' = dpStep w sums
            pruned = gcPrune target rem' sums'
        in (pruned, szs ++ [IS.size pruned])
        ) (IS.singleton 0, [1]) (zip weights suffixSums)
  in (sizes, IS.member target finalSet)

-- | DP with hard budget cap: after GC, if still > B, keep B closest to T
dpWithBudget :: [Int] -> Int -> Int -> ([Int], Bool)
dpWithBudget weights target budget =
  let suffixSums = tail $ scanr (+) 0 weights
      capToB sums =
        if IS.size sums <= budget then sums
        else let lst = IS.toList sums
                 scored = sortBy (comparing (\s -> abs (s - target))) lst
                 kept = take budget scored
             in IS.fromList kept
      (finalSet, sizes) = foldl' (\(sums, szs) (w, rem') ->
        let sums' = dpStep w sums
            pruned = gcPrune target rem' sums'
            capped = capToB pruned
        in (capped, szs ++ [IS.size capped])
        ) (IS.singleton 0, [1]) (zip weights suffixSums)
  in (sizes, IS.member target finalSet)

-- | Plain DP (no GC) for comparison: just track set size at each step
dpPlain :: [Int] -> Int -> ([Int], Bool)
dpPlain weights target =
  let (finalSet, sizes) = foldl' (\(sums, szs) w ->
        let sums' = dpStep w sums
        in (sums', szs ++ [IS.size sums'])
        ) (IS.singleton 0, [1]) weights
  in (sizes, IS.member target finalSet)

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
mkHashYes n =
  let (ws, _) = mkHash n
  in (ws, sum (take (n `div` 2) ws))

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int)
                / fromIntegral factor :: Double
  in show rounded

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn " GARBAGE COLLECTOR: grow the DP + prune dead sums at every step"
  putStrLn " Like Rust's ownership: if a sum can't reach T, drop it."
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Live set trajectory — watch the GC work
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. LIVE SET TRAJECTORY: plain DP vs GC-pruned DP ==="
  putStrLn "   (showing set size at each step after adding a weight)"
  putStrLn ""
  let n1 = 12
  let (ws1, t1) = mkHash n1
  let (plainSizes, plainOk) = dpPlain ws1 t1
      (gcSizes, gcOk) = dpWithGC ws1 t1
  putStrLn $ "n=" ++ show n1 ++ " target=" ++ show t1
    ++ " reachable=" ++ show plainOk
  putStrLn ""
  putStrLn $ padR 6 "step" ++ padR 14 "plain-DP" ++ padR 14 "GC-pruned"
    ++ padR 12 "pruned%"
  putStrLn (replicate 46 '-')
  mapM_ (\(i, p, g) -> do
    let pct = if p == 0 then 0
              else (1.0 - fromIntegral g / fromIntegral p) * 100 :: Double
    putStrLn $ padR 6 (show i) ++ padR 14 (show p) ++ padR 14 (show g)
      ++ padR 12 (showF 1 pct ++ "%")
    ) (zip3 [0 :: Int ..] plainSizes gcSizes)
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Peak live set — the critical metric
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. PEAK LIVE SET: does GC keep it polynomial? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "peak-plain" ++ padR 12 "peak-GC"
    ++ padR 10 "2^n" ++ padR 12 "GC/2^n" ++ padR 12 "GC/n^2"
  putStrLn (replicate 62 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (plainSz, _) = dpPlain ws t
        (gcSz, _) = dpWithGC ws t
        peakP = maximum plainSz
        peakG = maximum gcSz
        twoN = (2::Int)^n
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show peakP)
      ++ padR 12 (show peakG)
      ++ padR 10 (show twoN)
      ++ padR 12 (showF 4 (fromIntegral peakG / fromIntegral twoN :: Double))
      ++ padR 12 (showF 1 (fromIntegral peakG / fromIntegral (n*n) :: Double))
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Budget cap — minimum B for correct answer
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. BUDGET CAP: minimum B for correct answer ==="
  putStrLn "   (binary search for smallest B that still finds the target)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "peak-GC" ++ padR 12 "min-B-yes"
    ++ padR 10 "2^(n/2)" ++ padR 12 "B/2^(n/2)"
  putStrLn (replicate 50 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
        (gcSz, _) = dpWithGC ws t
        peakG = maximum gcSz
        -- Binary search for min budget
        test b = let (_, found) = dpWithBudget ws t b in found
        -- Search between 1 and peakG
        binSearch lo hi
          | lo >= hi  = lo
          | otherwise = let mid = (lo + hi) `div` 2
                        in if test mid then binSearch lo mid
                           else binSearch (mid + 1) hi
        minB = binSearch 1 (peakG + 1)
        halfN = (2::Int)^(n `div` 2)
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show peakG)
      ++ padR 12 (show minB)
      ++ padR 10 (show halfN)
      ++ padR 12 (showF 3 (fromIntegral minB / fromIntegral halfN :: Double))
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: The "Rust ownership" visualization
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. OWNERSHIP LIFECYCLE: birth, life, death of sums ==="
  putStrLn "   (for n=10, showing how many sums are born/killed per step)"
  putStrLn ""
  let n4 = 10
  let (ws4, t4) = mkHash n4
  let suffixSums4 = tail $ scanr (+) 0 ws4
  let trace = foldl' (\(sums, log') (step, w, rem') ->
        let before = IS.size sums
            afterAdd = dpStep w sums
            born = IS.size afterAdd - before
            afterGC = gcPrune t4 rem' afterAdd
            killed = IS.size afterAdd - IS.size afterGC
            alive = IS.size afterGC
        in (afterGC, log' ++ [(step, born, killed, alive)])
        ) (IS.singleton 0, [(0 :: Int, 0 :: Int, 0 :: Int, 1 :: Int)])
          (zip3 [1..] ws4 suffixSums4)
  putStrLn $ padR 6 "step" ++ padR 10 "born" ++ padR 10 "killed"
    ++ padR 10 "alive" ++ padR 20 "visual"
  putStrLn (replicate 56 '-')
  let (_, traceLog) = trace
  mapM_ (\(step, born, killed, alive) -> do
    let bar = replicate (alive `div` (max 1 (maximum (map (\(_,_,_,a)->a) traceLog) `div` 40))) '#'
    putStrLn $ padR 6 (show step) ++ padR 10 (show born)
      ++ padR 10 (show killed) ++ padR 10 (show alive)
      ++ padR 20 bar
    ) traceLog
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "ANALYSIS:"
  putStrLn " The GC (bound pruning) helps — it kills ~50% of sums at each step."
  putStrLn " But the live set still grows exponentially: GC reduces the CONSTANT"
  putStrLn " factor, not the EXPONENT. It's 0.6 × 2^n instead of 2^n."
  putStrLn ""
  putStrLn " Why? Because the GC only uses BOUNDS (min/max reachable)."
  putStrLn " To prune more, you'd need to know WHICH sums are reachable"
  putStrLn " — but that's the very problem you're trying to solve."
  putStrLn ""
  putStrLn " This is the circularity: efficient GC requires solving Subset Sum;"
  putStrLn " solving Subset Sum requires efficient GC."
  putStrLn "═══════════════════════════════════════════════════════════════════"
