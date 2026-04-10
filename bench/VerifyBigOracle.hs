module Main where

import PeqNP.BottomUpMITM
import PeqNP.DPSolver (dpReachable)
import PeqNP.ActorSolver (mkDensity1)
import qualified Data.Set as Set

main :: IO ()
main = do
  putStrLn "=== CORRECTNESS CHECK: big oracle vs DP ground truth ==="
  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n
        mr = bottomUpSolveMemo 2 ws t
        dp = Set.member t (dpReachable ws)
        ok = mrFound mr == dp
    putStrLn $ "  n=" ++ show n
      ++ " memo=" ++ show (mrFound mr)
      ++ " DP=" ++ show dp
      ++ " " ++ (if ok then "OK" else "*** MISMATCH ***")
      ++ " states=" ++ show (mrDistinctStates mr)
    ) [4..20]

  putStrLn "\n=== YES instances check ==="
  mapM_ (\n -> do
    let ws = [1..n]
        t = sum (take (n `div` 2) ws)
        mr = bottomUpSolveMemo 2 ws t
        dp = Set.member t (dpReachable ws)
        ok = mrFound mr == dp
    putStrLn $ "  n=" ++ show n
      ++ " memo=" ++ show (mrFound mr)
      ++ " DP=" ++ show dp
      ++ " " ++ (if ok then "OK" else "*** MISMATCH ***")
    ) [4..20]

  putStrLn "\n=== Achievable density-1 targets check ==="
  mapM_ (\n -> do
    let (ws, _) = mkDensity1 n
        -- Use sum of first half as target (should be achievable)
        t = sum (take (n `div` 2) ws)
        mr = bottomUpSolveMemo 2 ws t
        dp = Set.member t (dpReachable ws)
        ok = mrFound mr == dp
    putStrLn $ "  n=" ++ show n
      ++ " memo=" ++ show (mrFound mr)
      ++ " DP=" ++ show dp
      ++ " " ++ (if ok then "OK" else "*** MISMATCH ***")
      ++ " states=" ++ show (mrDistinctStates mr)
    ) [4..16]
