module Main where

import PeqNP.OracleSolver
import PeqNP.ActorSolver (mkDensityD, mkDensity1, padR, roundTo)
import PeqNP.MultiLevelSieve (recursiveRepSolveRaw)
import System.CPUTime
import Text.Printf

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " ORACLE SOLVER: suffix modular reachability → pruning"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: Scale ORACLE-ONLY BnB (skip plain for n>24, it's too slow)
  putStrLn "=== SCALING: Oracle BnB density 1 ==="
  putStrLn (padR 6 "n" ++ padR 14 "oracleNodes" ++ padR 10 "oPrunes"
            ++ padR 8 "found" ++ "time(s)")
  putStrLn (replicate 50 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n
    t0 <- getCPUTime
    let oracle = oracleSolve ws t
        !_ = orFound oracle
    t1 <- getCPUTime
    let oTime = fromIntegral (t1 - t0) / (1e12 :: Double)
    putStrLn $ padR 6 (show n)
      ++ padR 14 (show (orNodesTotal oracle))
      ++ padR 10 (show (orOraclePrunes oracle))
      ++ padR 8 (if orFound oracle then "YES" else "NO")
      ++ printf "%.3f" oTime
    ) [10, 14, 18, 20, 22, 24, 26, 28, 30]

  putStrLn ""

  -- Part 2: Oracle precheck — can it instantly prove NO?
  putStrLn "=== ORACLE PRECHECK (O(n) instant NO detection) ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 12 "precheck" ++ padR 12 "sieveWork"
            ++ "saved?")
  putStrLn (replicate 50 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        pc = oraclePrecheck ws t
        (_, sWork) = recursiveRepSolveRaw (max 4 (n `div` 4)) ws t
        saved = case pc of
          Just False -> "YES! (skipped sieve)"
          _          -> "no (sieve ran: work=" ++ show sWork
    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 12 (case pc of Just False -> "PROVED NO"; _ -> "inconclusive")
      ++ padR 12 (show sWork)
      ++ saved
    ) [ (20,1), (30,1), (40,1), (50,1)
      , (20,2), (30,2), (40,2), (50,2)
      , (20,5), (40,5), (60,5), (80,5), (100,5) ]

  putStrLn ""

  -- Part 3: Oracle precheck on random-looking targets
  putStrLn "=== ORACLE PRECHECK: various targets n=40 d=1 ==="
  let (ws40, _) = mkDensity1 40
      total40 = sum ws40
  mapM_ (\(t, desc) -> do
    let pc = oraclePrecheck ws40 t
    putStrLn $ "  target=" ++ padR 12 desc ++ " precheck="
      ++ (case pc of Just False -> "PROVED NO!"; _ -> "inconclusive")
    ) [ (total40 `div` 2, "sum/2")
      , (total40 `div` 2 + 1, "sum/2+1")
      , (total40 `div` 3, "sum/3")
      , (total40 `div` 5, "sum/5")
      , (total40 + 1, "sum+1")
      , (total40 + 7, "sum+7")
      , (12345, "12345")
      , (1, "1")
      ]

  putStrLn ""

  -- Part 4: Head-to-head with sieve for small n
  putStrLn "=== ORACLE BnB vs SIEVE (wall-clock, small n) ==="
  putStrLn (padR 6 "n" ++ padR 12 "oracle(s)" ++ padR 12 "sieve(s)"
            ++ padR 10 "faster" ++ "found?")
  putStrLn (replicate 55 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n

    t0 <- getCPUTime
    let o = oracleSolve ws t; !_ = orFound o
    t1 <- getCPUTime

    t2 <- getCPUTime
    let (sf, _) = recursiveRepSolveRaw (max 4 (n `div` 4)) ws t; !_ = sf
    t3 <- getCPUTime

    let oT = fromIntegral (t1 - t0) / (1e12 :: Double)
        sT = fromIntegral (t3 - t2) / (1e12 :: Double)
    putStrLn $ padR 6 (show n)
      ++ padR 12 (printf "%.4f" oT)
      ++ padR 12 (printf "%.4f" sT)
      ++ padR 10 (if oT < sT then "oracle" else "sieve")
      ++ (if orFound o then "YES" else "NO")
    ) [16, 18, 20, 22, 24, 26, 28, 30]

  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"
