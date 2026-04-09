module Main where

import PeqNP.ActorSolver
import PeqNP.MultiLevelSieve (recursiveRepSolveRaw, recursiveRepSolve, SolveResult(..),
                                bruteForceDP)
import Data.List (scanl')
import qualified Data.Set as Set

main :: IO ()
main = do
  putStrLn "==============================================================="
  putStrLn " HONEST BENCHMARK: buscando trampas y sesgos"
  putStrLn "==============================================================="
  putStrLn ""

  -- TEST 1: Are our instances YES or NO?
  putStrLn "=== TEST 1: Instancias YES vs NO ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 10 "found?" ++ padR 12 "work"
            ++ padR 12 "MITM" ++ "verified?")
  putStrLn (replicate 55 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        (found, work) = recursiveRepSolveRaw (max 4 (n `div` 4)) ws t
        mitm = 3 * (2 :: Int) ^ (n `div` 2)
        -- Verify with brute force only for small n
        verified = if n <= 20
                   then show (Set.member t (bruteForceDP ws)) ++ " (bf)"
                   else "n/a"
    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 10 (if found then "YES" else "NO")
      ++ padR 12 (show work)
      ++ padR 12 (showCompact mitm)
      ++ verified
    ) [ (10,1), (14,1), (20,1), (24,1), (28,1), (32,1), (36,1), (40,1)
      , (20,2), (30,2), (40,2), (50,2)
      , (20,5), (40,5), (60,5), (80,5), (100,5) ]

  putStrLn ""

  -- TEST 2: Fixed modulus 4 vs adaptive modulus
  -- This isolates whether the improvement is from the modulus or the algorithm
  putStrLn "=== TEST 2: Modulus fijo 4 vs adaptivo n/4 ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 12 "mod=4" ++ padR 12 "mod=n/4"
            ++ padR 10 "mod_val" ++ "faster?")
  putStrLn (replicate 55 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        (_, workFixed) = recursiveRepSolveRaw 4 ws t
        adaptiveMod = max 4 (n `div` 4)
        (_, workAdaptive) = recursiveRepSolveRaw adaptiveMod ws t
        faster = if workAdaptive < workFixed then "adaptive"
                 else if workFixed < workAdaptive then "fixed"
                 else "same"
    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 12 (show workFixed)
      ++ padR 12 (show workAdaptive)
      ++ padR 10 (show adaptiveMod)
      ++ faster
    ) [ (20,1), (24,1), (28,1), (32,1), (36,1), (40,1)
      , (20,2), (30,2), (40,2), (50,2)
      , (20,5), (40,5), (60,5), (80,5) ]

  putStrLn ""

  -- TEST 3: Guaranteed NO instances (target = sum + 1, impossible)
  -- These MUST try all residues, so we see the WORST case.
  putStrLn "=== TEST 3: Instancias NO garantizadas (target = sum+1) ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 12 "work_NO" ++ padR 12 "work_YES"
            ++ padR 10 "ratio" ++ "found?")
  putStrLn (replicate 60 '-')
  mapM_ (\(n, d) -> do
    let (ws, tYes) = mkDensityD n d
        tNo = sum ws + 1  -- impossible target
        modulus = max 4 (n `div` 4)
        (foundYes, workYes) = recursiveRepSolveRaw modulus ws tYes
        (foundNo, workNo) = recursiveRepSolveRaw modulus ws tNo
        ratio = if workYes > 0
                then fromIntegral workNo / fromIntegral workYes :: Double
                else 0
    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 12 (show workNo)
      ++ padR 12 (show workYes)
      ++ padR 10 (show (roundTo 1 ratio) ++ "x")
      ++ "yes=" ++ (if foundYes then "Y" else "N")
      ++ " no=" ++ (if foundNo then "Y" else "N")
    ) [ (20,1), (24,1), (28,1), (32,1), (36,1), (40,1)
      , (20,2), (30,2), (40,2), (50,2)
      , (20,5), (40,5), (60,5), (80,5) ]

  putStrLn ""

  -- TEST 4: Hard NO instances (target = sum/2, which may or may not be achievable)
  -- vs random-looking targets in the valid range
  putStrLn "=== TEST 4: Targets variados dentro del rango valido ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 10 "target" ++ padR 10 "found?"
            ++ padR 12 "work" ++ "notes")
  putStrLn (replicate 60 '-')
  mapM_ (\(n, d) -> do
    let (ws, _) = mkDensityD n d
        totalS = sum ws
        modulus = max 4 (n `div` 4)
        targets = [ (totalS `div` 2, "sum/2")
                  , (totalS `div` 2 + 1, "sum/2+1")
                  , (totalS `div` 3, "sum/3")
                  , (totalS `div` 4, "sum/4")
                  , (totalS * 3 `div` 4, "3sum/4")
                  ]
    mapM_ (\(t, desc) -> do
      let (found, work) = recursiveRepSolveRaw modulus ws t
      putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
        ++ padR 10 desc
        ++ padR 10 (if found then "YES" else "NO")
        ++ padR 12 (show work)
        ++ ""
      ) targets
    putStrLn ""
    ) [ (20,1), (32,1), (40,1)
      , (40,2), (60,5) ]

  -- TEST 5: Effective exponent with fixed modulus 4 (fair comparison to BenchSieve)
  putStrLn "=== TEST 5: Exponente con modulus fijo 4 (comparable a BenchSieve) ==="
  let worksMod4 = [ let (ws, t) = mkDensityD n 1.0
                        (_, w) = recursiveRepSolveRaw 4 ws t
                    in (n, w) | n <- [20, 24, 28, 32, 36, 40] ]
  mapM_ (\(n, w) -> putStrLn $ "  n=" ++ padR 4 (show n) ++ " work=" ++ show w)
        worksMod4
  let (n1, w1) = head worksMod4
      (n2, w2) = last worksMod4
      expMod4 = logBase 2 (fromIntegral w2 / fromIntegral (max 1 w1))
                / fromIntegral (n2 - n1) :: Double
  putStrLn $ "  Effective exponent (mod=4): O(2^{" ++ show (roundTo 3 expMod4) ++ "n})"
  putStrLn $ "  (BenchSieve reporto O(2^{0.291n}) con mod=4)"
  putStrLn ""

  -- TEST 6: ALL THREE SOLVERS: plain sieve vs card-only vs card+reps
  putStrLn "=== TEST 6: TRIPLE COMPARISON (plain reps vs card-only vs card+reps) ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 11 "plainReps" ++ padR 11 "cardOnly"
            ++ padR 11 "card+reps" ++ padR 10 "best" ++ padR 8 "found" ++ "alive")
  putStrLn (replicate 75 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        modulus = max 4 (n `div` 4)
        (fP, wP) = recursiveRepSolveRaw modulus ws t
        (fC, wC) = cardinalitySieveSolve ws t
        (fR, wR) = cardinalityRepSolve modulus ws t
        pw = precomputeWeights ws
        levels = initLevels pw t
        alive = length [ls | ls <- levels, lsStatus ls /= LKilled]
        total = length levels
        best | wR > 0 && wR <= wP && wR <= wC = "crd+rep"
             | wC > 0 && wC <= wP             = "crdOnly"
             | otherwise                       = "plain"
    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 11 (show wP) ++ padR 11 (show wC) ++ padR 11 (show wR)
      ++ padR 10 best
      ++ padR 8 (if fP then "YES" else "NO")
      ++ show alive ++ "/" ++ show total
    ) [ (20,1), (24,1), (28,1), (32,1), (36,1), (40,1), (44,1), (48,1)
      , (20,2), (30,2), (40,2), (50,2), (60,2)
      , (20,5), (40,5), (60,5), (80,5) ]

  putStrLn ""

  -- TEST 7: Various targets — where does card+reps shine?
  putStrLn "=== TEST 7: Targets variados — card+reps vs plain reps ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 10 "target" ++ padR 8 "found"
            ++ padR 11 "plainReps" ++ padR 11 "card+reps" ++ "speedup")
  putStrLn (replicate 65 '-')
  mapM_ (\(n, d) -> do
    let (ws, _) = mkDensityD n d
        totalS = sum ws
        modulus = max 4 (n `div` 4)
        targets = [ (totalS `div` 2, "sum/2")
                  , (totalS `div` 2 + 1, "sum/2+1")
                  , (totalS `div` 3, "sum/3")
                  , (totalS `div` 5, "sum/5")
                  ]
    mapM_ (\(t, desc) -> do
      let (fP, wP) = recursiveRepSolveRaw modulus ws t
          (fR, wR) = cardinalityRepSolve modulus ws t
          speedup = if wR > 0
                    then fromIntegral wP / fromIntegral wR :: Double
                    else 0
      putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
        ++ padR 10 desc ++ padR 8 (if fR then "YES" else "NO")
        ++ padR 11 (show wP) ++ padR 11 (show wR)
        ++ show (roundTo 2 speedup) ++ "x"
      ) targets
    putStrLn ""
    ) [ (32,1), (40,1), (48,1), (40,2), (60,5) ]

  putStrLn "=== FIN ==="

showCompact :: Int -> String
showCompact x
  | x >= 1000000000 = show (x `div` 1000000000) ++ "G"
  | x >= 1000000    = show (x `div` 1000000) ++ "M"
  | x >= 1000       = show (x `div` 1000) ++ "K"
  | otherwise        = show x
