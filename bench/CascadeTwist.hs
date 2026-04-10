module Main where

-- CASCADE OF MÖBIUS TWISTS
--
-- k=1: standard DP, O(2^n)
-- k=2: MITM, O(2^{n/2})
-- k=4: 2-level MITM, O(2^{n/4}) per group + combination
-- k=n/log n: each group has log(n) elements, n sums per group
--
-- The dream: k = n/log n twists gives 2^{n/log n} which is SUB-EXPONENTIAL.
-- But: the COMBINATION of k groups costs O(n^k) in the worst case.
-- With modular compression mod M at each step: O(k * M * n) = poly if M = poly.
-- Catch: modular compression saturates for density-1.
--
-- This experiment: sweep k from 1 to n, measure total work at each k.
-- Find the sweet spot.

import qualified Data.IntSet as IS
import Data.List (foldl')
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- | Split a list into k roughly equal groups
chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk k xs
  | k <= 1    = [xs]
  | otherwise = let sz = max 1 (length xs `div` k)
                    (h, t) = splitAt sz xs
                in h : chunk (k - 1) t

-- | All subset sums of a small group
allSubsetSums :: [Int] -> IS.IntSet
allSubsetSums [] = IS.singleton 0
allSubsetSums (w:ws) = let rest = allSubsetSums ws
                       in IS.union rest (IS.map (+w) rest)

-- | EXACT cascade: split into k groups, enumerate each, combine via DP
-- Returns: (found, per_group_max_sums, peak_combo_states, total_work)
exactCascade :: [Int] -> Int -> Int -> (Bool, Int, Int, Int)
exactCascade weights target k =
  let groups = chunk k weights
      groupSums = map allSubsetSums groups
      maxPerGroup = maximum (map IS.size groupSums)
      -- Combine groups one by one via exact DP
      (finalSet, peakStates, totalWork) = foldl' (\(acc, peak, work) gs ->
        let newAcc = IS.fromList
              [a + b | a <- IS.toList acc, b <- IS.toList gs, a + b <= target]
            sz = IS.size newAcc
            w = IS.size acc * IS.size gs  -- operations this step
        in (newAcc, max peak sz, work + w)
        ) (IS.singleton 0, 1, 0) groupSums
  in (IS.member target finalSet, maxPerGroup, peakStates, totalWork)

-- | MODULAR cascade: same but track sums mod M at each step
-- Returns: (torus_reachable, peak_states, total_work)
modularCascade :: [Int] -> Int -> Int -> Int -> (Bool, Int, Int)
modularCascade weights target k modulus =
  let groups = chunk k weights
      groupSums = map (\g -> IS.map (`mod` modulus) (allSubsetSums g)) groups
      tMod = target `mod` modulus
      (finalSet, peakStates, totalWork) = foldl' (\(acc, peak, work) gs ->
        let newAcc = IS.fromList
              [(a + b) `mod` modulus | a <- IS.toList acc, b <- IS.toList gs]
            sz = IS.size newAcc
            w = IS.size acc * IS.size gs
        in (newAcc, max peak sz, work + w)
        ) (IS.singleton 0, 1, 0) groupSums
  in (IS.member tMod finalSet, peakStates, totalWork)

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
  putStrLn " CASCADE OF MÖBIUS TWISTS: k splits of the weight set"
  putStrLn " k=1 → brute force, k=2 → MITM, k=n/log n → sub-exponential?"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Sweep k for fixed n — find optimal split count
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. SWEEP k: total work vs number of groups (n=14) ==="
  putStrLn ""
  let (ws1, t1) = mkHashYes 14
  putStrLn $ padR 5 "k" ++ padR 8 "grp-sz" ++ padR 10 "per-grp"
    ++ padR 12 "peak-st" ++ padR 14 "total-work" ++ padR 8 "found"
  putStrLn (replicate 58 '-')
  mapM_ (\k -> do
    let (found, perGrp, peak, work) = exactCascade ws1 t1 k
        grpSz = 14 `div` k
    putStrLn $ padR 5 (show k) ++ padR 8 (show grpSz)
      ++ padR 10 (show perGrp)
      ++ padR 12 (show peak)
      ++ padR 14 (show work)
      ++ padR 8 (show found)
    ) [1, 2, 3, 4, 5, 7, 14]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Optimal k across different n
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. OPTIMAL k: which k minimizes work for each n? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 8 "best-k" ++ padR 10 "grp-sz"
    ++ padR 14 "min-work" ++ padR 12 "MITM-work" ++ padR 10 "speedup"
  putStrLn (replicate 60 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
        results = [(k, let (_, _, _, w) = exactCascade ws t k in w) | k <- [1..n], n `mod` k == 0 || k <= n]
        validResults = filter (\(_, w) -> w > 0) results
        (bestK, bestWork) = if null validResults then (1, 0)
                            else foldl1 (\(k1,w1) (k2,w2) -> if w1 <= w2 then (k1,w1) else (k2,w2)) validResults
        -- MITM work (k=2)
        (_, _, _, mitmWork) = exactCascade ws t 2
        speedup = if bestWork == 0 then 0
                  else fromIntegral mitmWork / fromIntegral bestWork :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 8 (show bestK)
      ++ padR 10 (show (n `div` max 1 bestK))
      ++ padR 14 (show bestWork)
      ++ padR 12 (show mitmWork)
      ++ padR 10 (showF 2 speedup ++ "x")
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Modular cascade — can we keep states bounded?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. MODULAR CASCADE: states capped at M (n=14) ==="
  putStrLn ""
  putStrLn $ padR 5 "k" ++ padR 8 "M" ++ padR 10 "peak-st"
    ++ padR 12 "work" ++ padR 8 "corr"
  putStrLn (replicate 44 '-')
  let (ws3, t3) = mkHashYes 14
      (exact3, _) = (True, 0 :: Int)  -- we know YES
  mapM_ (\(k, m) -> do
    let (modReach, peak, work) = modularCascade ws3 t3 k m
    putStrLn $ padR 5 (show k) ++ padR 8 (show m)
      ++ padR 10 (show peak)
      ++ padR 12 (show work)
      ++ padR 8 (if modReach then "yes" else "no")
    ) [(2, 97), (3, 97), (4, 97), (7, 97), (14, 97),
       (2, 997), (3, 997), (7, 997), (14, 997)]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: The scaling law — work vs k for various n
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. SCALING LAW: log₂(work) vs k ==="
  putStrLn "   (looking for the minimum — the optimal number of twists)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 8 "k=1" ++ padR 8 "k=2"
    ++ padR 8 "k=3" ++ padR 8 "k=4" ++ padR 8 "k=n/2" ++ padR 8 "k=n"
  putStrLn (replicate 54 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
        workAt k = let (_, _, _, w) = exactCascade ws t k in w
        lg w = if w <= 0 then 0 else ceiling (logBase 2 (fromIntegral (max 1 w)) :: Double) :: Int
    putStrLn $ padR 5 (show n)
      ++ padR 8 (show (lg (workAt 1)))
      ++ padR 8 (show (lg (workAt 2)))
      ++ padR 8 (show (lg (workAt 3)))
      ++ padR 8 (show (lg (workAt 4)))
      ++ padR 8 (show (lg (workAt (n `div` 2))))
      ++ padR 8 (show (lg (workAt n)))
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: The n/log n prediction
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. THE PREDICTION: k = n/log₂(n) ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 8 "logn" ++ padR 8 "k*" ++ padR 10 "grp-sz"
    ++ padR 10 "per-grp" ++ padR 14 "work" ++ padR 12 "2^(n/2)"
  putStrLn (replicate 68 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
        logn = max 1 (ceiling (logBase 2 (fromIntegral n) :: Double) :: Int)
        kStar = max 1 (n `div` logn)
        (found, perGrp, _, work) = exactCascade ws t kStar
        mitm = (2::Int)^(n `div` 2)
    putStrLn $ padR 5 (show n)
      ++ padR 8 (show logn)
      ++ padR 8 (show kStar)
      ++ padR 10 (show (n `div` max 1 kStar))
      ++ padR 10 (show perGrp)
      ++ padR 14 (show work)
      ++ padR 12 (show mitm)
    ) [6, 8, 10, 12, 14, 16]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "ANALYSIS:"
  putStrLn " Each twist halves the per-group enumeration but the COMBINATION"
  putStrLn " step grows. There's a sweet spot."
  putStrLn ""
  putStrLn " Theory says: k = n/log n gives 2^{O(n/log n)} total — sub-exponential."
  putStrLn " But the combination's EXACT cost depends on how many intermediate"
  putStrLn " states survive at each level."
  putStrLn ""
  putStrLn " With modular compression (M = poly): combination is poly per level"
  putStrLn " but FALSE POSITIVES accumulate across levels."
  putStrLn " With exact combination: no false positives but states explode."
  putStrLn ""
  putStrLn " The million-dollar gap: between the modular (poly but wrong)"
  putStrLn " and the exact (correct but exponential), there MIGHT exist"
  putStrLn " a compression that's both poly AND correct."
  putStrLn " THAT is P vs NP."
  putStrLn "═══════════════════════════════════════════════════════════════════"
