module Main where

import PeqNP.ParallelSolver
import PeqNP.ActorSolver (mkDensityD, padR, roundTo, mkDensity1)
import PeqNP.MultiLevelSieve (recursiveRepSolveRaw)
import System.CPUTime
import Text.Printf
import qualified Data.Set as Set
import Data.List (foldl')

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " PARALLEL SOLVER BENCHMARK"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: Race orderings — which ordering wins?
  putStrLn "=== RACE ORDERINGS ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 10 "found?" ++ padR 30 "winner" ++ "time(s)")
  putStrLn (replicate 60 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
    t0 <- getCPUTime
    pr <- raceOrders ws t
    t1 <- getCPUTime
    let elapsed = fromIntegral (t1 - t0) / (1e12 :: Double)
    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 10 (if prFound pr then "YES" else "NO")
      ++ padR 30 (prMethod pr)
      ++ printf "%.3f" elapsed
    ) [ (20,1), (24,1), (28,1), (32,1)
      , (20,2), (24,2), (28,2), (32,2)
      , (20,5), (24,5), (28,5), (32,5) ]

  putStrLn ""

  -- Part 2: Parallel prefix search — early termination effect
  putStrLn "=== PARALLEL PREFIX SEARCH ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 10 "found?" ++ padR 40 "method" ++ "time(s)")
  putStrLn (replicate 70 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
    t0 <- getCPUTime
    pr <- parallelPrefixSearch ws t
    t1 <- getCPUTime
    let elapsed = fromIntegral (t1 - t0) / (1e12 :: Double)
    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 10 (if prFound pr then "YES" else "NO")
      ++ padR 40 (prMethod pr)
      ++ printf "%.3f" elapsed
    ) [ (20,1), (24,1), (28,1), (30,1), (32,1), (34,1), (36,1)
      , (28,2), (32,2), (36,2), (40,2)
      , (28,5), (32,5), (36,5), (40,5) ]

  putStrLn ""

  -- Part 3: HEAD-TO-HEAD: parallel prefix vs sieve vs sequential BnB
  putStrLn "=== HEAD-TO-HEAD: parallel vs sieve vs sequential ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 8 "found"
            ++ padR 12 "par(s)" ++ padR 12 "sieve(s)" ++ padR 12 "seq(s)"
            ++ "winner")
  putStrLn (replicate 70 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d

    -- Parallel prefix
    t0 <- getCPUTime
    prPar <- parallelPrefixSearch ws t
    t1 <- getCPUTime
    let parTime = fromIntegral (t1 - t0) / (1e12 :: Double)

    -- Sieve (no verification)
    t2 <- getCPUTime
    let (foundSieve, _workSieve) = recursiveRepSolveRaw (max 4 (n `div` 4)) ws t
    t3 <- seq foundSieve getCPUTime
    let sieveTime = fromIntegral (t3 - t2) / (1e12 :: Double)

    -- Sequential BnB
    t4 <- getCPUTime
    let foundSeq = seqBnBLocal ws t
    t5 <- seq foundSeq getCPUTime
    let seqTime = fromIntegral (t5 - t4) / (1e12 :: Double)

    let winner | parTime <= sieveTime && parTime <= seqTime = "parallel"
               | sieveTime <= parTime && sieveTime <= seqTime = "sieve"
               | otherwise = "sequential"

    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 8 (if prFound prPar then "YES" else "NO")
      ++ padR 12 (printf "%.4f" parTime)
      ++ padR 12 (printf "%.4f" sieveTime)
      ++ padR 12 (printf "%.4f" seqTime)
      ++ winner
    ) [ (20,1), (24,1), (28,1), (30,1)
      , (20,2), (24,2), (28,2), (30,2)
      , (20,5), (24,5), (28,5), (30,5) ]

  putStrLn ""

  -- Part 4: YES instances specifically (target = sum/2, which is often YES)
  putStrLn "=== YES INSTANCES: parallel speedup ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 8 "found"
            ++ padR 12 "par(s)" ++ padR 12 "seq(s)" ++ padR 10 "speedup")
  putStrLn (replicate 55 '-')
  mapM_ (\(n, d) -> do
    let (ws, _) = mkDensityD n d
        t = sum ws `div` 2  -- often a YES instance
    t0 <- getCPUTime
    prPar <- parallelPrefixSearch ws t
    t1 <- getCPUTime
    let parTime = fromIntegral (t1 - t0) / (1e12 :: Double)

    t2 <- getCPUTime
    let foundSeq = seqBnBLocal ws t
    t3 <- seq foundSeq getCPUTime
    let seqTime = fromIntegral (t3 - t2) / (1e12 :: Double)

    let speedup = if parTime > 0 then seqTime / parTime else 0

    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 8 (if prFound prPar then "YES" else "NO")
      ++ padR 12 (printf "%.4f" parTime)
      ++ padR 12 (printf "%.4f" seqTime)
      ++ padR 10 (show (roundTo 1 speedup) ++ "x")
    ) [ (24,1), (28,1), (30,1), (32,1)
      , (28,2), (32,2), (36,2)
      , (28,5), (32,5), (36,5), (40,5) ]

  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"

-- Sequential BnB (local copy for timing)
seqBnBLocal :: [Int] -> Int -> Bool
seqBnBLocal weights target = go 0 weights (sum weights)
  where
    go partial [] _ = partial == target
    go partial _ _ | partial > target = False
    go partial (x:xs) restSum
      | partial + restSum < target = False
      | otherwise = go (partial + x) xs (restSum - x)
                    || go partial xs (restSum - x)
