module Main where

{-
  RANDOM MARKERS: modular fingerprints for Subset Sum pruning

  Idea (from user): use random "anchors" to partition and prune the search
  space. Instead of one monolithic 2^n explosion, create controlled
  micro-explosions by discarding groups that can't possibly work.

  Implementation: for each small prime p, compute
    R_p = {Σ(subset) mod p : all subsets}  — via DP in O(n·p)
  A target T is reachable → T mod p ∈ R_p (necessary condition).
  Multiple primes compound: false positive rate ≈ ∏(|R_p|/p).

  Two uses:
    1. PRE-FILTER: reject impossible targets in O(n · Σp_i)
    2. MITM-PRUNE: skip left-half sums during meet-in-middle
       when (T - s_L) mod p ∉ R_p(right half)

  KEY QUESTION: does the pruning % scale with n?
    - If savings% → 100%: markers tame the exponential
    - If savings% → 0%: exponential wins, markers are futile
    - If constant: nice constant-factor speedup, still exponential
-}

import qualified Data.Set as Set
import qualified Data.IntSet as IS
import Data.List (foldl')
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- | Reachable residues mod p for a set of weights. O(n·p).
reachableModP :: [Int] -> Int -> IS.IntSet
reachableModP weights p =
  foldl' (\acc w ->
    IS.union acc (IS.map (\r -> (r + w) `mod` p) acc)
  ) (IS.singleton 0) weights

-- | Does target pass all modular filters?
passesAllFilters :: [(Int, IS.IntSet)] -> Int -> Bool
passesAllFilters filters target =
  all (\(p, residues) -> IS.member (target `mod` p) residues) filters

-- | Full reachable set via DP (ground truth, exponential)
dpReachable :: [Int] -> Set.Set Int
dpReachable = foldl' (\acc w -> Set.union acc (Set.map (+w) acc)) (Set.singleton 0)

-- | All subset sums of a list (brute force via IntSet)
allSubsetSums :: [Int] -> IS.IntSet
allSubsetSums [] = IS.singleton 0
allSubsetSums (w:ws) = let rest = allSubsetSums ws
                       in IS.union rest (IS.map (+w) rest)

-- | Vanilla MITM: split, enumerate halves, match
-- Returns: (found, leftSize, lookups)
mitmVanilla :: [Int] -> Int -> (Bool, Int, Int)
mitmVanilla weights target =
  let n = length weights
      (leftW, rightW) = splitAt (n `div` 2) weights
      leftSums  = allSubsetSums leftW
      rightSums = allSubsetSums rightW
      (found, looked) = IS.foldl' (\(f, lk) sL ->
        if f then (f, lk)
        else let needed = target - sL
             in if needed < 0 then (f, lk)
                else (IS.member needed rightSums, lk + 1)
        ) (False, 0) leftSums
  in (found, IS.size leftSums, looked)

-- | MITM with modular marker pruning
-- For each left sum sL, check (T - sL) mod p ∈ R_p(right) BEFORE expensive lookup
-- Returns: (found, leftSize, prunedCount, actualLookups)
mitmPruned :: [Int] -> Int -> [Int] -> (Bool, Int, Int, Int)
mitmPruned weights target primes =
  let n = length weights
      (leftW, rightW) = splitAt (n `div` 2) weights
      leftSums  = allSubsetSums leftW
      rightSums = allSubsetSums rightW
      -- Build modular filters for RIGHT half only
      rightFilters = [(p, reachableModP rightW p) | p <- primes]
      -- For each left sum, check filters before expensive lookup
      (found, pruned, looked) = IS.foldl' (\(f, pr, lk) sL ->
        if f then (f, pr, lk)
        else let needed = target - sL
             in if needed < 0 then (f, pr + 1, lk)
                else if not (passesAllFilters rightFilters needed)
                     then (f, pr + 1, lk)  -- pruned by marker!
                     else (IS.member needed rightSums, pr, lk + 1)
        ) (False, 0, 0) leftSums
  in (found, IS.size leftSums, pruned, looked)

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
      t = sum (take (n `div` 2) ws)
  in (ws, t)

smallPrimes :: [Int]
smallPrimes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
               59, 61, 67, 71, 73, 79, 83, 89, 97]

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int)
                / fromIntegral factor :: Double
  in show rounded

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn " RANDOM MARKERS: modular fingerprints for Subset Sum pruning"
  putStrLn " Can entropic sketches tame the exponential beast?"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Residue saturation — how much does each prime buy?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. RESIDUE SATURATION: |R_p|/p for density-1 weights ==="
  putStrLn "   (ratio → 1 means the prime provides ZERO pruning)"
  putStrLn ""
  let testPrimes1 = [3, 7, 13, 29, 53, 97]
  putStrLn $ padR 5 "n" ++ concatMap (\p -> padR 10 ("p=" ++ show p)) testPrimes1
  putStrLn (replicate 65 '-')
  mapM_ (\n -> do
    let (ws, _) = mkHash n
    putStr $ padR 5 (show n)
    mapM_ (\p -> do
      let rp = reachableModP ws p
          ratio = fromIntegral (IS.size rp) / fromIntegral p :: Double
      putStr $ padR 10 (showF 3 ratio)
      ) testPrimes1
    putStrLn ""
    ) [6, 8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Combined filter power — k primes together
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. COMBINED FILTER: fraction of [0..T] surviving k primes ==="
  putStrLn "   (compare with actual reachable fraction from DP)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "actual" ++ padR 12 "k=3"
    ++ padR 12 "k=6" ++ padR 12 "k=10" ++ padR 12 "k=15"
  putStrLn (replicate 65 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        actual = dpReachable ws
        actualFrac = fromIntegral (Set.size actual) / fromIntegral (t + 1) :: Double
        testTargets = [0..t]
        countSurviving k =
          let filters = [(p, reachableModP ws p) | p <- take k smallPrimes]
              survivors = length (filter (passesAllFilters filters) testTargets)
          in fromIntegral survivors / fromIntegral (length testTargets) :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 12 (showF 4 actualFrac)
      ++ padR 12 (showF 4 (countSurviving 3))
      ++ padR 12 (showF 4 (countSurviving 6))
      ++ padR 12 (showF 4 (countSurviving 10))
      ++ padR 12 (showF 4 (countSurviving 15))
    ) [6, 8, 10]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Pre-filter for NO instances — how fast can we reject?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. PRE-FILTER: how many primes to reject a NO-instance? ==="
  putStrLn ""
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        primeResults = map (\p ->
          let rp = reachableModP ws p
          in (p, IS.member (t `mod` p) rp)
          ) smallPrimes
        firstReject = filter (not . snd) primeResults
    putStrLn $ "  n=" ++ show n ++ " target=" ++ show t
    if null firstReject
      then putStrLn "    Target passes ALL modular filters (looks reachable to markers)"
      else let (p, _) = head firstReject
               idx = length (takeWhile snd primeResults) + 1
           in putStrLn $ "    REJECTED at prime p=" ++ show p
                ++ " (filter #" ++ show idx ++ " of " ++ show (length smallPrimes) ++ ")"
                ++ " cost: O(n·" ++ show (sum (map fst (take idx primeResults))) ++ ")"
    ) [6, 8, 10, 12, 14, 16]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: MITM pruning — the main event
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. MITM PRUNING: markers reduce matching lookups ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 12 "van-look"
    ++ padR 12 "prn-look" ++ padR 12 "pruned" ++ padR 10 "save%"
  putStrLn (replicate 58 '-')
  mapM_ (\n -> do
    let primes = take 8 smallPrimes
    -- NO instance
    let (wsN, tN) = mkHash n
        (_, _, vanLookN) = mitmVanilla wsN tN
        (_, _, markerPrunedN, prunedLookN) = mitmPruned wsN tN primes
        savingsN = if vanLookN == 0 then 0
                   else (1.0 - fromIntegral prunedLookN
                             / fromIntegral vanLookN) * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 12 (show vanLookN)
      ++ padR 12 (show prunedLookN)
      ++ padR 12 (show markerPrunedN)
      ++ padR 10 (showF 1 savingsN ++ "%")
    -- YES instance
    let (wsY, tY) = mkHashYes n
        (_, _, vanLookY) = mitmVanilla wsY tY
        (_, _, markerPrunedY, prunedLookY) = mitmPruned wsY tY primes
        savingsY = if vanLookY == 0 then 0
                   else (1.0 - fromIntegral prunedLookY
                             / fromIntegral vanLookY) * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 12 (show vanLookY)
      ++ padR 12 (show prunedLookY)
      ++ padR 12 (show markerPrunedY)
      ++ padR 10 (showF 1 savingsY ++ "%")
    ) [8, 10, 12, 14, 16, 18]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: Scaling — the critical question
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. SCALING: does pruning % grow, shrink, or stay flat? ==="
  putStrLn "   (this determines if markers change the complexity class)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "2^(n/2)" ++ padR 12 "van-look"
    ++ padR 12 "prn-look" ++ padR 10 "save%" ++ padR 14 "marker-cost"
  putStrLn (replicate 64 '-')
  mapM_ (\n -> do
    let primes = take 10 smallPrimes
        (ws, t) = mkHash n
        (_, _, vanLook) = mitmVanilla ws t
        (_, _, _, prunedLook) = mitmPruned ws t primes
        savings = if vanLook == 0 then 0
                  else (1.0 - fromIntegral prunedLook
                            / fromIntegral vanLook) * 100 :: Double
        filterCost = n * sum (take 10 smallPrimes)
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show ((2::Int)^(n `div` 2)))
      ++ padR 12 (show vanLook)
      ++ padR 12 (show prunedLook)
      ++ padR 10 (showF 1 savings ++ "%")
      ++ padR 14 (show filterCost)
    ) [8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "VERDICT:"
  putStrLn " savings% → 100% as n grows  →  markers tame the exponential"
  putStrLn " savings% → constant          →  nice speedup, still exponential"
  putStrLn " savings% → 0% as n grows    →  exponential wins, markers futile"
  putStrLn ""
  putStrLn "The residue saturation (Section 1) is the leading indicator:"
  putStrLn " if |R_p|/p → 1 for all p, modular markers carry no information."
  putStrLn "═══════════════════════════════════════════════════════════════════"
