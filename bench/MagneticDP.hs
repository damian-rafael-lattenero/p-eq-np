module Main where

{-
  MAGNETIC DP: use a "magnetic field" to attract partial sums toward T

  Standard DP keeps ALL reachable sums (exponential).
  GC-pruned DP keeps sums in a WINDOW around T (still exponential).

  Magnetic DP: keep only the top-B sums ranked by "magnetic score" —
  the probability of reaching T from this partial sum given remaining weights.

  The "magnetic field" is Gaussian:
    score(s, k) ∝ exp(-(T - s - μ_rem)² / (2·σ²_rem))
  where μ_rem = Σ w_j / 2, σ²_rem = Σ w_j² / 4 (remaining weights)

  This is physically: the CLT says remaining subset sums are ~Gaussian,
  so the probability that remaining sums fill the gap (T - s) is Gaussian.

  Multiple "magnet" types compared:
    1. NAIVE: keep B sums closest to T (distance magnet)
    2. GAUSSIAN: keep B sums with highest P(reach T | s, remaining)
    3. MODULAR: keep B sums most compatible with T mod small primes
    4. COMBINED: all three signals multiplied

  KEY QUESTION: what budget B gives correct answers?
    B = O(n²) → POLYNOMIAL!
    B = O(2^{n/2}) → same as MITM
    B = O(2^n) → magnet is useless
-}

import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import Data.List (foldl', sortBy, take, tails)
import Data.Ord (comparing, Down(..))
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- | Gaussian score: how likely is it to reach T from partial sum s,
-- given remaining weights ws_remaining?
gaussianScore :: Int -> Int -> [Int] -> Double
gaussianScore target s remaining =
  let gap = fromIntegral (target - s) :: Double
      mu  = fromIntegral (sum remaining) / 2.0
      var = sum [fromIntegral (w * w) | w <- remaining] / 4.0
      sigma = max 1.0 (sqrt var)
  in if var < 1.0 then if abs (gap - mu) < 1 then 1.0 else 0.0
     else exp (-(gap - mu)**2 / (2.0 * var))

-- | Distance score: how close is s to T?
distanceScore :: Int -> Int -> Double
distanceScore target s = 1.0 / (1.0 + fromIntegral (abs (target - s)))

-- | Modular score: how many primes does (T - s) mod p match reachable residues?
modularScore :: Int -> Int -> [Int] -> [Int] -> Double
modularScore target s remaining primes =
  let gap = target - s
      matches = sum [if any (\r -> (gap - r) `mod` p == 0) [0, p-1..p*2]
                        then 0 else 1  -- simplified: just check if gap mod p is 0
                    | p <- primes]
      -- Actually: check if gap mod p is achievable by remaining
      matchCount = length $ filter (\p ->
        let needed = gap `mod` p
            reachable = foldl' (\acc w ->
              IS.union acc (IS.map (\r -> (r + w) `mod` p) acc)
              ) (IS.singleton 0) remaining
        in IS.member needed reachable
        ) primes
  in fromIntegral matchCount / fromIntegral (max 1 (length primes))

-- | Combined score
combinedScore :: Int -> Int -> [Int] -> [Int] -> Double
combinedScore target s remaining primes =
  gaussianScore target s remaining
  * distanceScore target s
  * (0.1 + modularScore target s remaining primes)

-- | Magnetic DP: add weights one by one, keep top-B sums by score
magneticDP :: [Int] -> Int -> Int                -- weights, target, budget
           -> (Int -> Int -> [Int] -> Double)    -- scoring function
           -> (Bool, Int, Int)                   -- (found, final_set_size, steps)
magneticDP weights target budget scorer =
  let n = length weights
      go :: IS.IntSet -> [Int] -> [[Int]] -> Int -> (Bool, Int, Int)
      go sums [] _ step = (IS.member target sums, IS.size sums, step)
      go sums (w:ws) remaining step
        | IS.member target sums = (True, IS.size sums, step)
        | otherwise =
            let curRemaining = case remaining of
                                (r:_) -> r
                                []    -> []
                -- Add weight w
                newSums = IS.union sums (IS.map (+w) sums)
                -- Score all sums
                scored = sortBy (comparing (Down . snd))
                  [(s, scorer target s curRemaining) | s <- IS.toList newSums, s <= target]
                -- Keep top B (plus sums > target are dropped)
                kept = IS.fromList $ take budget $ map fst scored
                -- Always keep 0 and target if present
                kept' = (if IS.member target newSums then IS.insert target else id)
                      $ IS.insert 0 kept
            in go kept' ws (drop 1 remaining) (step + 1)
      -- Build list of remaining-weight-lists: [[w2..wn], [w3..wn], ..., []]
      remainingLists = drop 1 (tails weights)
  in go (IS.singleton 0) weights remainingLists 1

-- | Exact DP (for ground truth)
exactDP :: [Int] -> Int -> Bool
exactDP ws t = IS.member t $ foldl' (\acc w -> IS.union acc (IS.map (+w) acc)) (IS.singleton 0) ws

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
  putStrLn " MAGNETIC DP: attract partial sums toward T with a scoring field"
  putStrLn " Keep only top-B sums by 'magnetic score' at each step"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Which magnet works best? (fixed budget B=n²)
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. MAGNET COMPARISON: B=n², which scorer finds T? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 10 "distance"
    ++ padR 10 "gaussian" ++ padR 10 "combined" ++ padR 8 "exact"
  putStrLn (replicate 50 '-')
  mapM_ (\n -> do
    let b = n * n
        primes = [3, 5, 7, 11, 13]
    -- YES
    let (wsY, tY) = mkHashYes n
        (dY, _, _) = magneticDP wsY tY b (\t s _ -> distanceScore t s)
        (gY, _, _) = magneticDP wsY tY b (\t s r -> gaussianScore t s r)
        (cY, _, _) = magneticDP wsY tY b (\t s r -> combinedScore t s r primes)
        eY = exactDP wsY tY
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 10 (show dY)
      ++ padR 10 (show gY)
      ++ padR 10 (show cY)
      ++ padR 8 (show eY)
    -- NO
    let (wsN, tN) = mkHash n
        (dN, _, _) = magneticDP wsN tN b (\t s _ -> distanceScore t s)
        (gN, _, _) = magneticDP wsN tN b (\t s r -> gaussianScore t s r)
        (cN, _, _) = magneticDP wsN tN b (\t s r -> combinedScore t s r primes)
        eN = exactDP wsN tN
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 10 (show dN)
      ++ padR 10 (show gN)
      ++ padR 10 (show cN)
      ++ padR 8 (show eN)
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Minimum budget for correctness (Gaussian magnet)
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. MIN BUDGET: smallest B where Gaussian magnet is correct ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 10 "B=n" ++ padR 10 "B=n²"
    ++ padR 10 "B=n³" ++ padR 10 "B=2^(n/2)" ++ padR 8 "exact"
  putStrLn (replicate 60 '-')
  mapM_ (\n -> do
    let scorer t s r = gaussianScore t s r
    -- YES
    let (wsY, tY) = mkHashYes n
        test b = let (f, _, _) = magneticDP wsY tY b scorer in f
        eY = exactDP wsY tY
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 10 (show (test n))
      ++ padR 10 (show (test (n*n)))
      ++ padR 10 (show (test (n*n*n)))
      ++ padR 10 (show (test ((2::Int)^(n `div` 2))))
      ++ padR 8 (show eY)
    -- NO
    let (wsN, tN) = mkHash n
        testN b = let (f, _, _) = magneticDP wsN tN b scorer in f
        eN = exactDP wsN tN
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 10 (show (testN n))
      ++ padR 10 (show (testN (n*n)))
      ++ padR 10 (show (testN (n*n*n)))
      ++ padR 10 (show (testN ((2::Int)^(n `div` 2))))
      ++ padR 8 (show eN)
    ) [6, 8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: How strong is the magnet? (survival rate of solution path)
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. MAGNET STRENGTH: does the solution path survive pruning? ==="
  putStrLn "   For YES instances: tracking whether partial solutions stay in top-B"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 8 "budget" ++ padR 10 "survives" ++ padR 14 "final_size"
  putStrLn (replicate 38 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
    mapM_ (\bMult -> do
      let b = bMult * n
          (found, sz, _) = magneticDP ws t b (\tgt s r -> gaussianScore tgt s r)
      putStrLn $ padR 5 (show n) ++ padR 8 (show b)
        ++ padR 10 (show found)
        ++ padR 14 (show sz)
      ) [1, 2, 4, 8]
    ) [8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: Scaling — does min-B grow polynomially?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. SCALING: binary search for min correct B (Gaussian) ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "min-B" ++ padR 10 "n²"
    ++ padR 10 "2^(n/2)" ++ padR 12 "B/n²" ++ padR 12 "B/2^(n/2)"
  putStrLn (replicate 58 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
        test b = let (f, _, _) = magneticDP ws t b (\tgt s r -> gaussianScore tgt s r) in f
        binSearch lo hi
          | lo >= hi  = lo
          | otherwise = let mid = (lo + hi) `div` 2
                        in if test mid then binSearch lo mid
                           else binSearch (mid + 1) hi
        maxB = (2::Int)^(n `div` 2) + 1
        minB = binSearch 1 maxB
        halfN = (2::Int)^(n `div` 2)
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show minB)
      ++ padR 10 (show (n*n))
      ++ padR 10 (show halfN)
      ++ padR 12 (showF 2 (fromIntegral minB / fromIntegral (n*n) :: Double))
      ++ padR 12 (showF 4 (fromIntegral minB / fromIntegral halfN :: Double))
    ) [6, 8, 10, 12]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "VERDICT:"
  putStrLn " min-B / n² → constant : MAGNET GIVES POLYNOMIAL ALGORITHM!"
  putStrLn " min-B / 2^(n/2) → constant : same as MITM (magnet = no help)"
  putStrLn " min-B / 2^n → constant : magnet is completely useless"
  putStrLn ""
  putStrLn " The magnet's power = how much signal (solution path) stands out"
  putStrLn " from noise (random partial sums with similar Gaussian score)."
  putStrLn " For density-1: solutions are 'cryptographically hidden' in noise."
  putStrLn "═══════════════════════════════════════════════════════════════════"
