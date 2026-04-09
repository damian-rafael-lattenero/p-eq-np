module Main where

import PeqNP.StructuralSolver
  ( solve, solveAliased, SolveResult(..), showSolveResult, MatchType(..)
  , enumerateHalf, PreNode(..), injectAliases
  )
import PeqNP.ActorSolver (mkDensity1, mkDensityD, mkHardDensity1, padR, roundTo)
import PeqNP.OracleSolver (oraclePrecheck)
import System.CPUTime
import Text.Printf

-- ═══════════════════════════════════════════════════════════
-- p-eq-np: Subset Sum Solver
--
-- Based on: "Beyond Worst-Case Subset Sum" (Salas, 2503.20162)
--
-- Algorithm: Double Meet-in-the-Middle with
--   1. Half-enumeration (subsets of size ≤ n/4 per half)
--   2. On-the-fly matching (check during right-side construction)
--   3. Four complement match types (Lemmas 1-5 of the paper)
--   4. Canonical collision pruning (unique sums only)
--
-- Complexity:
--   O*(U · n²) deterministic, where U = |Σ(S)| = unique subset sums
--   Early exit on YES instances (often work = 1 matching check)
-- ═══════════════════════════════════════════════════════════

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " p-eq-np: Adaptive Subset Sum Solver"
  putStrLn " Algorithm: Half-Enum + On-The-Fly MITM + Complement Matching"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─── Small examples ───────────────────────────────────────
  putStrLn "=== SMALL EXAMPLES ==="
  putStrLn ""
  let demo ws t = do
        let r = solve ws t
        putStrLn $ "  " ++ show ws ++ " target=" ++ show t
        putStrLn $ "  → " ++ showSolveResult r
        putStrLn ""
  demo [3, 7, 5, 2] 10
  demo [3, 7, 5, 2] 12
  demo [3, 7, 5, 2] 11
  demo [1, 2, 3, 4, 5, 6] 15
  demo [10, 20, 30, 40, 50] 60
  demo [10, 20, 30, 40, 50] 99

  -- ─── Scaling across densities ─────────────────────────────
  putStrLn "=== SOLVER PERFORMANCE ACROSS n AND DENSITY ==="
  putStrLn (padR 5 "n" ++ padR 4 "d" ++ padR 8 "found"
            ++ padR 10 "work" ++ padR 10 "early"
            ++ padR 8 "U_L" ++ padR 8 "U_R" ++ "match")
  putStrLn (replicate 65 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        r = solve ws t
    putStrLn $ padR 5 (show n) ++ padR 4 (show (round d :: Int))
      ++ padR 8 (if solFound r then "YES" else "NO")
      ++ padR 10 (show (solTotalEnum r))
      ++ padR 10 (show (solWorkDone r))
      ++ padR 8 (show (solLeftU r))
      ++ padR 8 (show (solRightU r))
      ++ maybe "—" show (solMatchType r)
    ) [ (10,1), (14,1), (18,1), (20,1), (24,1), (28,1), (32,1)
      , (10,2), (14,2), (18,2), (20,2), (24,2), (28,2), (32,2)
      , (10,5), (14,5), (18,5), (20,5), (24,5), (28,5), (32,5)
      , (10,10), (14,10), (18,10), (20,10), (24,10), (28,10), (32,10) ]
  putStrLn ""

  -- ─── Timing at scale ──────────────────────────────────────
  putStrLn "=== TIMING AT SCALE (density-1) ==="
  putStrLn (padR 5 "n" ++ padR 12 "time_ms" ++ padR 10 "U_total"
            ++ padR 8 "found")
  putStrLn (replicate 40 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n
    t0 <- getCPUTime
    let !r = solve ws t
        !_ = solFound r
    t1 <- getCPUTime
    let ms = fromIntegral (t1 - t0) / 1e9 :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 12 (printf "%.1f" ms)
      ++ padR 10 (show (solTotalEnum r))
      ++ padR 8 (if solFound r then "YES" else "NO")
    ) [16, 20, 24, 28, 32, 36, 40]
  putStrLn ""

  -- ─── Unique sums compression ──────────────────────────────
  putStrLn "=== UNIQUE SUMS COMPRESSION (U vs 2^{n/2}) ==="
  putStrLn (padR 5 "n" ++ padR 4 "d" ++ padR 12 "U_half"
            ++ padR 14 "2^{n/2}" ++ padR 10 "compress")
  putStrLn (replicate 50 '-')
  mapM_ (\(n, d) -> do
    let (ws, _) = mkDensityD n d
        mid = n `div` 2
        halfSize = max 1 (n `div` 4)
        leftW = take mid ws
        node = enumerateHalf halfSize leftW
        u = pnUniqueCount node
        full = 2 ^ mid :: Int
        ratio = fromIntegral u / fromIntegral (max 1 full) :: Double
    putStrLn $ padR 5 (show n) ++ padR 4 (show (round d :: Int))
      ++ padR 12 (show u)
      ++ padR 14 (if mid <= 20 then show full else "2^" ++ show mid)
      ++ padR 10 (show (roundTo 2 ratio))
    ) [ (20,1), (24,1), (28,1), (32,1)
      , (20,2), (24,2), (28,2), (32,2)
      , (20,5), (24,5), (28,5), (32,5)
      , (20,10), (24,10), (28,10), (32,10) ]
  putStrLn ""

  -- ─── Oracle integration ───────────────────────────────────
  putStrLn "=== ORACLE + SOLVER COMBO ==="
  putStrLn (padR 5 "n" ++ padR 4 "d" ++ padR 12 "oracle"
            ++ padR 8 "found" ++ padR 10 "work" ++ "match")
  putStrLn (replicate 50 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        oCheck = oraclePrecheck ws t
        r = case oCheck of
              Just False -> SolveResult False Nothing Nothing 0 0 0 0
              _          -> solve ws t
        oStr = case oCheck of
          Just False -> "PRUNED"
          _          -> "pass"
    putStrLn $ padR 5 (show n) ++ padR 4 (show (round d :: Int))
      ++ padR 12 oStr
      ++ padR 8 (if solFound r then "YES" else "NO")
      ++ padR 10 (show (solTotalEnum r))
      ++ maybe "—" show (solMatchType r)
    ) [ (20,1), (24,1), (28,1), (32,1)
      , (20,5), (24,5), (28,5), (32,5) ]

  putStrLn ""

  -- ─── Hard instances: LCG vs hash-mixed ─────────────────────
  putStrLn "=== LCG (structured) vs HASH-MIXED (hard) INSTANCES ==="
  putStrLn (padR 5 "n" ++ padR 10 "lcg_U" ++ padR 10 "hard_U"
            ++ padR 10 "lcg_ms" ++ padR 10 "hard_ms" ++ "ratio")
  putStrLn (replicate 55 '-')
  mapM_ (\n -> do
    let (ws1, t1) = mkDensity1 n
        (ws2, t2) = mkHardDensity1 n
    ta <- getCPUTime
    let !r1 = solve ws1 t1; !_ = solFound r1
    tb <- getCPUTime
    let !r2 = solve ws2 t2; !_ = solFound r2
    tc <- getCPUTime
    let ms1 = fromIntegral (tb - ta) / 1e9 :: Double
        ms2 = fromIntegral (tc - tb) / 1e9 :: Double
        rat = if ms1 > 0.01 then ms2 / ms1 else 0
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show (solTotalEnum r1))
      ++ padR 10 (show (solTotalEnum r2))
      ++ padR 10 (printf "%.1f" ms1)
      ++ padR 10 (printf "%.1f" ms2)
      ++ (if rat > 0 then printf "%.1fx" rat else "n/a")
    ) [20, 24, 28, 32, 36, 40, 44]
  putStrLn ""

  -- ─── Controlled aliasing: U reduction measurement ─────────
  putStrLn "=== ALIASING: U REDUCTION PER HALF (left half only) ==="
  putStrLn (padR 5 "n" ++ padR 4 "δ" ++ padR 10 "U_norm"
            ++ padR 10 "U_alias" ++ padR 10 "reduction")
  putStrLn (replicate 45 '-')
  mapM_ (\(n, delta) -> do
    let (ws, _) = mkHardDensity1 n
        mid = n `div` 2
        halfSize = max 1 (n `div` 4)
        leftW = take mid ws
        normalU  = pnUniqueCount (enumerateHalf halfSize leftW)
        aliasedW = injectAliases delta leftW
        aliasedU = pnUniqueCount (enumerateHalf halfSize aliasedW)
        reduction = if normalU > 0
                    then 1.0 - fromIntegral aliasedU / fromIntegral normalU :: Double
                    else 0
    putStrLn $ padR 5 (show n) ++ padR 4 (show delta)
      ++ padR 10 (show normalU)
      ++ padR 10 (show aliasedU)
      ++ padR 10 (printf "%.1f%%" (reduction * 100))
    ) [ (24,0), (24,1), (24,2), (24,3)
      , (28,0), (28,1), (28,2), (28,3)
      , (32,0), (32,1), (32,2), (32,3)
      , (36,0), (36,1), (36,2), (36,3) ]

  putStrLn ""

  -- ─── Controlled aliasing: full solver timing ──────────────
  putStrLn "=== ALIASING: SOLVER TIMING (hard density-1) ==="
  putStrLn (padR 5 "n" ++ padR 4 "δ" ++ padR 10 "time_ms"
            ++ padR 8 "found" ++ padR 10 "U_report")
  putStrLn (replicate 45 '-')
  mapM_ (\(n, delta) -> do
    let (ws, t) = mkHardDensity1 n
    t0 <- getCPUTime
    let !r = solveAliased delta ws t; !_ = solFound r
    t1 <- getCPUTime
    let ms = fromIntegral (t1 - t0) / 1e9 :: Double
    putStrLn $ padR 5 (show n) ++ padR 4 (show delta)
      ++ padR 10 (printf "%.1f" ms)
      ++ padR 8 (if solFound r then "YES" else "NO")
      ++ padR 10 (show (solTotalEnum r))
    ) [ (28,0), (28,1), (28,2), (28,3)
      , (32,0), (32,1), (32,2), (32,3) ]

  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"
