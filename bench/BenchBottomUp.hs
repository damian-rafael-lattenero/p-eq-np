module Main where

import PeqNP.BottomUpMITM
import PeqNP.OracleSolver (oracleSolve, OracleResult(..), plainBnB)
import PeqNP.LazyTree (searchWithStats, PruneStats(..))
import PeqNP.StructuralSolver (solve, SolveResult(..))
import PeqNP.DPSolver (dpReachable)
import PeqNP.ActorSolver (mkDensity1, mkDensityD, padR)
import qualified Data.Set as Set
import System.CPUTime
import Text.Printf

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " BOTTOM-UP MITM: cardinality-exact + complement + oracle"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: Correctness verification
  putStrLn "=== CORRECTNESS: bottomUpSolve vs dpReachable ==="
  let allOk = and [ let (ws, t) = mkDensity1 n
                        bu = bottomUpSolve 2 ws t
                        dp = Set.member t (dpReachable ws)
                    in buFound bu == dp
                  | n <- [4..16] ]
  putStrLn $ "  All n=4..16: " ++ if allOk then "PASS" else "FAIL"

  -- Also test YES instances (target = sum of first half)
  let yesOk = and [ let ws = [1..n]
                        t = sum (take (n `div` 2) ws)
                        bu = bottomUpSolve 2 ws t
                    in buFound bu && case buSolution bu of
                         Just sol -> sum sol == t
                         Nothing -> False
                  | n <- [4..20] ]
  putStrLn $ "  YES instances n=4..20: " ++ if yesOk then "PASS" else "FAIL"
  putStrLn ""

  -- Part 2: Pruning breakdown (density-1, moderate n)
  putStrLn "=== PRUNING BREAKDOWN (density-1) ==="
  putStrLn (padR 5 "n" ++ padR 10 "nodes" ++ padR 8 "sing"
    ++ padR 8 "pair" ++ padR 8 "compl" ++ padR 8 "oracle"
    ++ padR 8 "bound" ++ padR 14 "match")
  putStrLn (replicate 70 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n
        bu = bottomUpSolve 2 ws t
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show (buNodesExplored bu))
      ++ padR 8 (show (buSingletonHits bu))
      ++ padR 8 (show (buPairHits bu))
      ++ padR 8 (show (buComplHits bu))
      ++ padR 8 (show (buOracleHits bu))
      ++ padR 8 (show (buBoundHits bu))
      ++ padR 14 (maybe "none" show (buMatchType bu))
    ) [6, 8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

  -- Part 3: Head-to-head node counts
  putStrLn "=== NODE COUNTS: BU vs Oracle vs Plain vs LazyTree (density-1) ==="
  putStrLn (padR 5 "n"
    ++ padR 12 "BU" ++ padR 12 "Oracle" ++ padR 12 "Plain"
    ++ padR 12 "Lazy" ++ padR 8 "found")
  putStrLn (replicate 63 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n

    t0 <- getCPUTime
    let bu = bottomUpSolve 2 ws t; !_ = buFound bu
    t1 <- getCPUTime
    let buTime = fromIntegral (t1 - t0) / (1e12 :: Double)

    -- Only run expensive solvers for small n
    let (oNodes, pNodes, lNodes) = if n <= 22
          then let o = oracleSolve ws t
                   p = plainBnB ws t
                   l = searchWithStats ws t
               in (show (orNodesTotal o), show (orNodesTotal p), show (psNodesExplored l))
          else ("skip", "skip", "skip")

    putStrLn $ padR 5 (show n)
      ++ padR 12 (show (buNodesExplored bu))
      ++ padR 12 oNodes
      ++ padR 12 pNodes
      ++ padR 12 lNodes
      ++ padR 8 (if buFound bu then "YES" else "NO")
    ) [8, 10, 12, 14, 16, 18, 20, 22, 24]
  putStrLn ""

  -- Part 4: YES instances (where BU should excel with early exit)
  putStrLn "=== YES INSTANCES: BU vs Oracle (sequential weights) ==="
  putStrLn (padR 5 "n" ++ padR 12 "BU-nodes" ++ padR 12 "Oracle-nodes"
    ++ padR 14 "BU-match" ++ padR 10 "speedup")
  putStrLn (replicate 55 '-')
  mapM_ (\n -> do
    let ws = [1..n]
        t = sum (take (n `div` 2) ws)  -- target = sum of first half
        bu = bottomUpSolve 2 ws t
        o  = oracleSolve ws t
        speedup = if buNodesExplored bu > 0
                  then fromIntegral (orNodesTotal o) / fromIntegral (buNodesExplored bu) :: Double
                  else 0
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show (buNodesExplored bu))
      ++ padR 12 (show (orNodesTotal o))
      ++ padR 14 (maybe "none" show (buMatchType bu))
      ++ padR 10 (printf "%.1fx" speedup)
    ) [10, 20, 30, 40, 50, 60, 80, 100]
  putStrLn ""

  -- Part 5: High density
  putStrLn "=== HIGH DENSITY (d=5): BU nodes ==="
  putStrLn (padR 5 "n" ++ padR 12 "BU-nodes" ++ padR 12 "Oracle-nodes"
    ++ padR 14 "BU-match" ++ padR 8 "found")
  putStrLn (replicate 55 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDensityD n 5
        bu = bottomUpSolve 2 ws t
        o  = oracleSolve ws t
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show (buNodesExplored bu))
      ++ padR 12 (show (orNodesTotal o))
      ++ padR 14 (maybe "none" show (buMatchType bu))
      ++ padR 8 (if buFound bu then "YES" else "NO")
    ) [10, 20, 30, 40, 50]

  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"
