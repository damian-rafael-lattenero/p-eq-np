module Main where

import PeqNP.ActorSolver

main :: IO ()
main = do
  putStrLn "=== ACTOR SOLVER BENCHMARK (sequential) ==="
  putStrLn ""

  -- Part 1: Work comparison
  let results = map actorBenchmark [6, 8, 10, 12, 14, 16, 18, 20]
  putStrLn (showActorBenchmark results)

  -- Part 2: Level detail for selected sizes
  putStrLn ""
  putStrLn "=== LEVEL DETAIL ==="
  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n
        ar = actorSolveSequential ws t
    putStrLn $ "\nn=" ++ show n ++ " target=" ++ show t
    putStrLn (showActorResult ar)
    ) [8, 12, 16]
