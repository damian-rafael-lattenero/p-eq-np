module Main where

import PeqNP.ActorSolver
import qualified Data.Set as Set

main :: IO ()
main = do
  putStrLn "=== ACTOR SOLVER CORRECTNESS VERIFICATION ==="
  putStrLn ""

  -- Test sequential solver against brute force for multiple targets per n
  let testN n = do
        let (ws, t) = mkDensity1 n
            -- Test the density-1 target
            ar1 = actorSolveSequential ws t
            -- Test target = 0 (always reachable)
            ar0 = actorSolveSequential ws 0
            -- Test impossible target
            arBig = actorSolveSequential ws (sum ws + 1)
            -- Test all single-element targets
            arSingles = [actorSolveSequential ws w | w <- ws]
            allCorrect = arCorrect ar1 && arCorrect ar0 && arCorrect arBig
                         && all arCorrect arSingles
        putStrLn $ "  n=" ++ padR 3 (show n)
          ++ " density1:" ++ showOk (arCorrect ar1)
          ++ " zero:" ++ showOk (arCorrect ar0)
          ++ " impossible:" ++ showOk (arCorrect arBig)
          ++ " singles:" ++ showOk (all arCorrect arSingles)
          ++ (if allCorrect then " ALL OK" else " *** ERRORS ***")

  putStrLn "--- Sequential solver ---"
  mapM_ testN [4, 6, 8, 10, 12, 14, 16, 18, 20]

  -- Test dpByCardinality against brute force
  putStrLn ""
  putStrLn "--- dpByCardinality vs brute force ---"
  mapM_ (\n -> do
    let (ws, _) = mkDensity1 n
        -- All cardinalities via DP
        dpAll = dpAllCardinalities ws
        -- All reachable via brute force
        bfAll = localBruteForceDP ws
        -- Union of all cardinality sets should equal brute force
        dpUnion = foldMap id dpAll
        match = dpUnion == bfAll
    putStrLn $ "  n=" ++ padR 3 (show n)
      ++ " |dpUnion|=" ++ padR 8 (show (Set.size dpUnion))
      ++ " |bf|=" ++ padR 8 (show (Set.size bfAll))
      ++ " " ++ showOk match
    ) [4, 6, 8, 10, 12]

  putStrLn ""
  putStrLn "Done."

-- local copy to avoid import issues
localBruteForceDP :: [Int] -> Set.Set Int
localBruteForceDP = foldl (\s w -> Set.union s (Set.map (+ w) s)) (Set.singleton 0)

showOk :: Bool -> String
showOk True  = "OK"
showOk False = "ERR"
