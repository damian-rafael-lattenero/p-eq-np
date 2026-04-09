module Main where

import PeqNP.ResidualGraph
import PeqNP.ActorSolver (mkDensity1, mkDensityD, padR, roundTo)
import PeqNP.OracleSolver (oracleSolve, plainBnB, OracleResult(..))

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " RESIDUAL GRAPH: structural decomposition of Subset Sum"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: Visualize small examples
  putStrLn "=== SMALL EXAMPLES (graph structure) ==="
  putStrLn ""

  let ex1 = buildResidualGraph [1,3,5] 8
  putStrLn (showGraph ex1)
  putStrLn $ "  " ++ graphStats ex1
  putStrLn $ "  bfs:     " ++ showSearchResult (bfsSearch ex1)
  putStrLn $ "  greedy:  " ++ showSearchResult (greedySearch ex1)
  putStrLn $ "  chain:   " ++ showSearchResult (residualChainSearch ex1)
  putStrLn ""

  let ex2 = buildResidualGraph [3,7,5,2] 10
  putStrLn (showGraph ex2)
  putStrLn $ "  " ++ graphStats ex2
  putStrLn $ "  bfs:     " ++ showSearchResult (bfsSearch ex2)
  putStrLn $ "  greedy:  " ++ showSearchResult (greedySearch ex2)
  putStrLn $ "  chain:   " ++ showSearchResult (residualChainSearch ex2)
  putStrLn ""

  -- NO instance
  let ex3 = buildResidualGraph [3,7,5,2] 11
  putStrLn $ "=== NO instance: [3,7,5,2] target=11 ==="
  putStrLn $ "  " ++ graphStats (buildResidualGraph [3,7,5,2] 11)
  putStrLn $ "  bfs:     " ++ showSearchResult (bfsSearch ex3)
  putStrLn $ "  chain:   " ++ showSearchResult (residualChainSearch ex3)
  putStrLn ""

  -- Part 2: Residual graph search vs Oracle BnB vs Plain BnB
  putStrLn "=== RESIDUAL CHAIN vs ORACLE BnB vs PLAIN BnB (density 1) ==="
  putStrLn (padR 6 "n" ++ padR 12 "chainNodes" ++ padR 12 "oracleNodes"
            ++ padR 12 "plainNodes" ++ padR 8 "found" ++ "graphSize")
  putStrLn (replicate 65 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n
        rg = buildResidualGraph ws t
        chain = residualChainSearch rg
        oracle = oracleSolve ws t
        plain = plainBnB ws t
    putStrLn $ padR 6 (show n)
      ++ padR 12 (show (srNodes chain))
      ++ padR 12 (show (orNodesTotal oracle))
      ++ padR 12 (show (orNodesTotal plain))
      ++ padR 8 (if srFound chain then "YES" else "NO")
      ++ graphStats rg
    ) [10, 12, 14, 16, 18, 20, 22, 24]

  putStrLn ""

  -- Part 3: Density 2
  putStrLn "=== RESIDUAL CHAIN vs ORACLE BnB (density 2) ==="
  putStrLn (padR 6 "n" ++ padR 12 "chainNodes" ++ padR 12 "oracleNodes"
            ++ padR 8 "found" ++ "graphSize")
  putStrLn (replicate 55 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDensityD n 2.0
        rg = buildResidualGraph ws t
        chain = residualChainSearch rg
        oracle = oracleSolve ws t
    putStrLn $ padR 6 (show n)
      ++ padR 12 (show (srNodes chain))
      ++ padR 12 (show (orNodesTotal oracle))
      ++ padR 8 (if srFound chain then "YES" else "NO")
      ++ graphStats rg
    ) [10, 12, 14, 16, 18, 20, 22, 24]

  putStrLn ""

  -- Part 4: Density 5
  putStrLn "=== RESIDUAL CHAIN vs ORACLE BnB (density 5) ==="
  putStrLn (padR 6 "n" ++ padR 12 "chainNodes" ++ padR 12 "oracleNodes"
            ++ padR 8 "found" ++ "graphSize")
  putStrLn (replicate 55 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDensityD n 5.0
        rg = buildResidualGraph ws t
        chain = residualChainSearch rg
        oracle = oracleSolve ws t
    putStrLn $ padR 6 (show n)
      ++ padR 12 (show (srNodes chain))
      ++ padR 12 (show (orNodesTotal oracle))
      ++ padR 8 (if srFound chain then "YES" else "NO")
      ++ graphStats rg
    ) [10, 12, 14, 16, 18, 20, 22, 24]

  putStrLn ""

  -- Part 5: Various targets
  putStrLn "=== VARIOUS TARGETS n=20 d=1 ==="
  let (ws20, _) = mkDensity1 20
      total20 = sum ws20
  putStrLn (padR 10 "target" ++ padR 12 "chainNodes" ++ padR 12 "oracleNodes"
            ++ padR 8 "found")
  putStrLn (replicate 45 '-')
  mapM_ (\(t, desc) -> do
    let rg = buildResidualGraph ws20 t
        chain = residualChainSearch rg
        oracle = oracleSolve ws20 t
    putStrLn $ padR 10 desc
      ++ padR 12 (show (srNodes chain))
      ++ padR 12 (show (orNodesTotal oracle))
      ++ padR 8 (if srFound chain then "YES" else "NO")
    ) [ (total20 `div` 2, "sum/2")
      , (total20 `div` 2 + 1, "sum/2+1")
      , (total20 `div` 3, "sum/3")
      , (total20 `div` 5, "sum/5")
      , (0, "0")
      ]

  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"
