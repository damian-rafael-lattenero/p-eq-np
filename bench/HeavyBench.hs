module Main where

import PeqNP.ActorSolver
import PeqNP.MultiLevelSieve (recursiveRepSolveRaw, recursiveRepSolve, SolveResult(..))
import System.CPUTime
import Text.Printf

main :: IO ()
main = do
  putStrLn "==============================================================="
  putStrLn " HEAVY BENCHMARK: Hybrid (level-killing + sieve) vs Sieve-only"
  putStrLn "==============================================================="
  putStrLn ""

  -- Part 1: Density 1 (weights ~ 2^n, hardest regime)
  putStrLn "--- DENSITY 1 (weights ~ 2^n) ---"
  putStrLn header
  putStrLn (replicate 85 '-')
  mapM_ (runBench 1.0) [20, 24, 28, 32, 36, 40, 44, 48]

  putStrLn ""

  -- Part 2: Density 2 (weights ~ 2^(n/2))
  putStrLn "--- DENSITY 2 (weights ~ 2^(n/2)) ---"
  putStrLn header
  putStrLn (replicate 85 '-')
  mapM_ (runBench 2.0) [20, 30, 40, 50, 60]

  putStrLn ""

  -- Part 3: Density 5 (weights ~ 2^(n/5))
  putStrLn "--- DENSITY 5 (weights ~ 2^(n/5)) ---"
  putStrLn header
  putStrLn (replicate 85 '-')
  mapM_ (runBench 5.0) [20, 40, 60, 80, 100]

  putStrLn ""

  -- Part 4: Level killing analysis
  putStrLn "--- LEVEL KILLING EFFECTIVENESS ---"
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 10 "killed" ++ padR 10 "total"
            ++ padR 10 "%" ++ "killedAll?")
  putStrLn (replicate 55 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        hr = actorSieveHybrid 4 ws t
        total = hrKilled hr + hrAlive hr
        pct = if total == 0 then 0
              else (100 * hrKilled hr) `div` total
    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 10 (show (hrKilled hr)) ++ padR 10 (show total)
      ++ padR 10 (show pct ++ "%")
      ++ (if hrKilledAll hr then "YES" else "no")
    ) [ (20, 1), (30, 1), (40, 1), (50, 1)
      , (40, 2), (60, 2), (80, 2)
      , (60, 5), (80, 5), (100, 5) ]

  putStrLn ""

  -- Part 5: Growth rate analysis
  putStrLn "--- GROWTH RATE (effective exponent) ---"
  analyzeGrowth 1.0 [20, 24, 28, 32, 36, 40]
  analyzeGrowth 2.0 [20, 30, 40, 50, 60]
  analyzeGrowth 5.0 [20, 40, 60, 80, 100]

header :: String
header = padR 6 "n" ++ padR 12 "hybrid" ++ padR 12 "sieve"
  ++ padR 14 "MITM" ++ padR 10 "killed" ++ padR 10 "alive"
  ++ padR 8 "ok" ++ "time(s)"

runBench :: Double -> Int -> IO ()
runBench d n = do
  let (ws, t) = mkDensityD n d
      modulus = max 4 (n `div` 4)

  -- Timed hybrid
  t0 <- getCPUTime
  let hr = actorSieveHybrid modulus ws t
  -- Force evaluation
  let !_ = hrFound hr
      !_ = hrSieveWork hr
  t1 <- getCPUTime
  let elapsed = fromIntegral (t1 - t0) / (1e12 :: Double)

  -- Sieve-only (if n <= 24, also verify)
  let sieveWork = hrSieveWork hr  -- hybrid already ran the sieve
      mitm = 3 * (2 :: Int) ^ (n `div` 2)
      killed = hrKilled hr
      alive = hrAlive hr

  -- Correctness check only for small n
  ok <- if n <= 24
        then do
          let sr = recursiveRepSolve modulus ws t
          pure (srFound sr == hrFound hr)
        else pure True  -- trust correctness

  putStrLn $ padR 6 (show n)
    ++ padR 12 (show sieveWork)
    ++ padR 12 (show sieveWork)  -- same since hybrid runs sieve
    ++ padR 14 (showCompact mitm)
    ++ padR 10 (show killed ++ "/" ++ show (killed + alive))
    ++ padR 10 (show alive)
    ++ padR 8 (if ok then "OK" else "ERR")
    ++ printf "%.2f" elapsed

analyzeGrowth :: Double -> [Int] -> IO ()
analyzeGrowth d ns = do
  let works = [ let (ws, t) = mkDensityD n d
                    hr = actorSieveHybrid (max 4 (n `div` 4)) ws t
                in (n, hrSieveWork hr)
              | n <- ns ]
      -- Only use points where work > 0
      validWorks = [(n, w) | (n, w) <- works, w > 0]
  case validWorks of
    [] -> putStrLn $ "  d=" ++ show (round d :: Int) ++ ": no data"
    [(n, _)] -> putStrLn $ "  d=" ++ show (round d :: Int) ++ ": only 1 data point"
    _ -> do
      let (n1, w1) = head validWorks
          (n2, w2) = last validWorks
          exponent = if w1 > 0 && w2 > w1
                     then logBase 2 (fromIntegral w2 / fromIntegral w1)
                          / fromIntegral (n2 - n1) :: Double
                     else 0
      putStrLn $ "  d=" ++ show (round d :: Int)
        ++ " n=" ++ show n1 ++ "->" ++ show n2
        ++ " work=" ++ show w1 ++ "->" ++ show w2
        ++ " effective O(2^{" ++ printf "%.3f" exponent ++ "n})"

showCompact :: Int -> String
showCompact x
  | x >= 1000000000 = show (x `div` 1000000000) ++ "G"
  | x >= 1000000    = show (x `div` 1000000) ++ "M"
  | x >= 1000       = show (x `div` 1000) ++ "K"
  | otherwise        = show x
