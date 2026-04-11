module Main where

-- LAZY FUTURE: treat 2^{n/2} subset sums as lazy generators
--
-- Like Haskell's [1..] + take n — never materialize what you don't need.
--
-- Pipeline: generate → filter(bounds) → filter(modular) → find(target)
-- Each stage is LAZY: only pulls from upstream when downstream asks.
-- If find succeeds early, upstream generators STOP.
--
-- The question: how many elements are actually FORCED (materialized)?
-- If forced << 2^{n/2} → laziness beats eager enumeration.

import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM
import Data.List (foldl')
import Data.Bits (xor, shiftR)
import Data.IORef
import PeqNP.ActorSolver (padR)

-- ═══════════════════════════════════════════════════════════════
-- LAZY SUBSET SUM GENERATOR
-- ═══════════════════════════════════════════════════════════════

-- | Lazily generate all subset sums of weights[0..mid-1] as a list.
-- The ORDER matters: we generate in a way that applies bounds INLINE,
-- so branches that can't reach target are never entered.
--
-- This is a lazy tree traversal: each "node" is a thunk.
-- Forcing a node = deciding include/exclude one weight.
lazySubsetSums :: [Int] -> Int -> Int -> [Int]
-- weights, target, remaining_sum → lazy list of feasible partial sums
lazySubsetSums [] _ _ = [0]
lazySubsetSums (w:ws) target remaining =
  let remaining' = remaining - w
      -- Branch OUT: don't include w (if bounds still feasible)
      outsums = if remaining' >= 0  -- can still potentially reach target with rest
                then lazySubsetSums ws target remaining'
                else []
      -- Branch IN: include w (if doesn't overshoot)
      insums  = if w <= target  -- including w doesn't exceed target
                then map (+w) (lazySubsetSums ws (target - w) remaining')
                     -- ↑ Note: lazy map, nothing computed until consumed
                else []
  in outsums ++ insums
  -- Both branches are LAZY: ++ doesn't force either side

-- | Count how many elements of a lazy list are forced before finding target
-- (or exhausting the list)
countUntilFind :: Int -> [Int] -> (Bool, Int)
countUntilFind target = go 0
  where
    go !n [] = (False, n)
    go !n (x:xs)
      | x == target = (True, n + 1)
      | otherwise   = go (n + 1) xs

-- | Lazy pipeline: generate → filter(modular) → find(target)
lazyPipeline :: [Int] -> Int -> [Int] -> (Bool, Int, Int, Int)
-- weights, target, primes → (found, generated, passed_mod, total_forced)
lazyPipeline weights target primes =
  let n = length weights
      mid = n `div` 2
      leftW = take mid weights
      rightW = drop mid weights
      leftRemaining = sum leftW

      -- Stage 1: lazy generation with bounds (LEFT half)
      leftGen = lazySubsetSums leftW target leftRemaining

      -- Precompute right-half modular reachability for filtering
      rightModReach = [(p, reachModP rightW p) | p <- primes]

      -- Stage 2: modular filter (lazy!)
      modFilter s = all (\(p, reach) ->
        IS.member ((target - s) `mod` p) reach) rightModReach

      leftFiltered = filter modFilter leftGen

      -- Stage 3: build right sums and check (this is the "find")
      rightSums = foldl' (\acc w -> IS.union acc (IS.map (+w) acc)) (IS.singleton 0) rightW

      -- Count forced at each stage
      genCount = length leftGen           -- forces ALL of stage 1
      filtCount = length leftFiltered     -- forces stage 2

      -- The LAZY way: don't count all, find first match
      (found, forcedUntilFound) = countUntilFind target
        [s | s <- leftFiltered, IS.member (target - s) rightSums]

  in (found, genCount, filtCount, forcedUntilFound)

-- | Even LAZIER: don't enumerate right half either. For each left sum,
-- check if (target - leftSum) is achievable by right half using
-- LAZY right-half generation + modular prefilter.
fullyLazy :: [Int] -> Int -> [Int] -> (Bool, Int)
-- Returns: (found, total_nodes_forced)
fullyLazy weights target primes =
  let n = length weights
      mid = n `div` 2
      leftW = take mid weights
      rightW = drop mid weights
      leftRemaining = sum leftW
      rightRemaining = sum rightW

      -- Precompute modular oracles for BOTH halves
      leftModReach = [(p, reachModP leftW p) | p <- primes]
      rightModReach = [(p, reachModP rightW p) | p <- primes]

      -- Lazy left generator with bounds
      leftGen = lazySubsetSums leftW target leftRemaining

      -- For each left sum: lazily check if complement exists in right
      -- WITHOUT enumerating all right sums
      checkRight leftSum =
        let needed = target - leftSum
        in if needed < 0 || needed > rightRemaining then False
           else -- Modular precheck
                if not (all (\(p, reach) -> IS.member (needed `mod` p) reach) rightModReach)
                then False
                else -- Must enumerate right to be sure — but lazily!
                     needed `elem` lazySubsetSums rightW needed rightRemaining

      -- Lazy search: try each left sum, stop at first match
      go !count [] = (False, count)
      go !count (s:ss)
        | checkRight s = (True, count + 1)
        | otherwise    = go (count + 1) ss

  in go 0 leftGen

reachModP :: [Int] -> Int -> IS.IntSet
reachModP ws p = foldl' (\acc w ->
  IS.union acc (IS.map (\r -> (r + w) `mod` p) acc)) (IS.singleton 0) ws

-- | Eager MITM for comparison
eagerMITM :: [Int] -> Int -> (Bool, Int)
eagerMITM weights target =
  let mid = length weights `div` 2
      leftSums = foldl' (\acc w -> IS.union acc (IS.map (+w) acc)) (IS.singleton 0) (take mid weights)
      rightSums = foldl' (\acc w -> IS.union acc (IS.map (+w) acc)) (IS.singleton 0) (drop mid weights)
      found = IS.foldl' (\f s -> f || IS.member (target - s) rightSums) False leftSums
  in (found, IS.size leftSums + IS.size rightSums)

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
  putStrLn " LAZY FUTURE: subset sums as lazy generators"
  putStrLn " Like [1..] + take n — never materialize what you don't need"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  let primes = [3, 5, 7, 11, 13, 17, 19, 23]

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Fully lazy — how many nodes forced?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. FULLY LAZY: nodes forced to determine answer ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 12 "forced"
    ++ padR 10 "2^(n/2)" ++ padR 10 "ratio" ++ padR 10 "forced/n²"
  putStrLn (replicate 54 '-')
  mapM_ (\n -> do
    -- YES
    let (wsY, tY) = mkHashYes n
        (fY, forcedY) = fullyLazy wsY tY primes
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 12 (show forcedY)
      ++ padR 10 (show ((2::Int)^(n `div` 2)))
      ++ padR 10 (showF 4 (fromIntegral forcedY / fromIntegral ((2::Int)^(n `div` 2)) :: Double))
      ++ padR 10 (showF 2 (fromIntegral forcedY / fromIntegral (n*n) :: Double))
    -- NO
    let (wsN, tN) = mkHash n
        (fN, forcedN) = fullyLazy wsN tN primes
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 12 (show forcedN)
      ++ padR 10 (show ((2::Int)^(n `div` 2)))
      ++ padR 10 (showF 4 (fromIntegral forcedN / fromIntegral ((2::Int)^(n `div` 2)) :: Double))
      ++ padR 10 (showF 2 (fromIntegral forcedN / fromIntegral (n*n) :: Double))
    ) [8, 10, 12, 14, 16, 18]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Comparison with eager MITM
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. LAZY vs EAGER: total work comparison ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 12 "lazy"
    ++ padR 12 "eager" ++ padR 10 "speedup" ++ padR 8 "match"
  putStrLn (replicate 54 '-')
  mapM_ (\n -> do
    -- YES
    let (wsY, tY) = mkHashYes n
        (fLY, lazyY) = fullyLazy wsY tY primes
        (fEY, eagerY) = eagerMITM wsY tY
        spY = fromIntegral eagerY / fromIntegral (max 1 lazyY) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 12 (show lazyY) ++ padR 12 (show eagerY)
      ++ padR 10 (showF 1 spY ++ "x")
      ++ padR 8 (if fLY == fEY then "OK" else "ERR")
    -- NO
    let (wsN, tN) = mkHash n
        (fLN, lazyN) = fullyLazy wsN tN primes
        (fEN, eagerN) = eagerMITM wsN tN
        spN = fromIntegral eagerN / fromIntegral (max 1 lazyN) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 12 (show lazyN) ++ padR 12 (show eagerN)
      ++ padR 10 (showF 1 spN ++ "x")
      ++ padR 8 (if fLN == fEN then "OK" else "ERR")
    ) [8, 10, 12, 14, 16]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: YES early termination — how fast does lazy find it?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. EARLY TERMINATION: forced before YES found ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "forced" ++ padR 10 "2^(n/2)"
    ++ padR 12 "forced/n" ++ padR 10 "forced/n²"
  putStrLn (replicate 50 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
        (_, forced) = fullyLazy ws t primes
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show forced)
      ++ padR 10 (show ((2::Int)^(n `div` 2)))
      ++ padR 12 (showF 2 (fromIntegral forced / fromIntegral n :: Double))
      ++ padR 10 (showF 2 (fromIntegral forced / fromIntegral (n*n) :: Double))
    ) [8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: The scaling question
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. SCALING: forced(NO) / 2^{n/2} ==="
  putStrLn "   → 0 : lazy avoids exponential enumeration!"
  putStrLn "   → 1 : lazy = eager, no benefit"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "forced-NO" ++ padR 10 "2^(n/2)"
    ++ padR 10 "ratio"
  putStrLn (replicate 38 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (_, forced) = fullyLazy ws t primes
        halfN = (2::Int)^(n `div` 2)
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show forced)
      ++ padR 10 (show halfN)
      ++ padR 10 (showF 4 (fromIntegral forced / fromIntegral halfN :: Double))
    ) [8, 10, 12, 14, 16, 18]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "INSIGHT:"
  putStrLn " For YES instances: lazy finds the answer in O(?) forced nodes."
  putStrLn "   If forced/n → const: YES is O(n)!"
  putStrLn "   If forced/n → grows: YES is super-linear"
  putStrLn ""
  putStrLn " For NO instances: lazy must prove ALL paths fail."
  putStrLn "   forced ≈ 2^{n/2} typically (no early termination possible)"
  putStrLn ""
  putStrLn " The asymmetry: YES can short-circuit, NO cannot."
  putStrLn " This is the NP vs co-NP question in microcosm."
  putStrLn "═══════════════════════════════════════════════════════════════════"
