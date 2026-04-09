module Main where

import PeqNP.StructuralSolver
import PeqNP.ActorSolver (mkDensity1, mkDensityD, padR, roundTo)
import PeqNP.MultiLevelSieve (recursiveRepSolveRaw)
import System.CPUTime
import Text.Printf
import qualified Data.IntMap.Strict as IM

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " STRUCTURAL SOLVER: Result ↔ PreNode meeting via IntMap"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: Small examples to see the structure
  putStrLn "=== SMALL EXAMPLES ==="
  putStrLn ""

  let demo ws t = do
        let left = enrichList (take (length ws `div` 2) ws)
            right = enrichList (drop (length ws `div` 2) ws)
            result = enrichTarget t left
            matched = meet result right
            dm = doubleMITM ws t
        putStrLn $ "  " ++ show ws ++ " target=" ++ show t
        putStrLn $ "  left PreNode:  U=" ++ show (pnUniqueCount left)
                   ++ " sums=" ++ show (IM.keys (pnSums left))
        putStrLn $ "  right PreNode: U=" ++ show (pnUniqueCount right)
                   ++ " sums=" ++ show (IM.keys (pnSums right))
        putStrLn $ "  Result needs from right: " ++ show (rNeeded result)
        putStrLn $ "  MEETING hits: " ++ show (rHits matched)
                   ++ " (count=" ++ show (rHitCount matched) ++ ")"
        putStrLn $ "  doubleMITM: " ++ showDoubleMITMResult dm
        putStrLn ""

  demo [1,3,5] 8
  demo [3,7,5,2] 10
  demo [3,7,5,2] 11
  demo [1,2,3,4,5,6] 15
  demo [10,20,30,40,50] 60

  -- Part 2: U (unique sums) vs 2^n — where is the compression?
  putStrLn "=== UNIQUE SUMS (U) vs 2^n — compression ratio ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 12 "U" ++ padR 14 "2^n"
            ++ padR 10 "ratio" ++ "compression")
  putStrLn (replicate 55 '-')
  mapM_ (\(n, d) -> do
    let (ws, _) = mkDensityD n d
        node = enrichList ws
        u = pnUniqueCount node
        twoN = 2 ^ n :: Int
        ratio = fromIntegral u / fromIntegral (max 1 twoN) :: Double
    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 12 (show u)
      ++ padR 14 (if n <= 20 then show twoN else "2^" ++ show n)
      ++ padR 10 (if n <= 20 then show (roundTo 4 ratio) else "n/a")
      ++ (if ratio < 0.5 then "GOOD" else if ratio < 0.9 then "some" else "none")
    ) [ (10,1), (12,1), (14,1), (16,1), (18,1), (20,1)
      , (10,2), (12,2), (14,2), (16,2), (18,2), (20,2)
      , (10,5), (12,5), (14,5), (16,5), (18,5), (20,5) ]

  putStrLn ""

  -- Part 3: Double MITM performance
  putStrLn "=== DOUBLE MITM: Result↔PreNode vs plain sieve ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 10 "dmWork" ++ padR 10 "sieveW"
            ++ padR 10 "speedup" ++ padR 8 "found" ++ padR 8 "leftU" ++ "rightU")
  putStrLn (replicate 70 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        dm = doubleMITM ws t
        (_, sW) = recursiveRepSolveRaw (max 4 (n `div` 4)) ws t
        speedup = if dmTotalWork dm > 0
                  then fromIntegral sW / fromIntegral (dmTotalWork dm) :: Double
                  else 0
    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 10 (show (dmTotalWork dm))
      ++ padR 10 (show sW)
      ++ padR 10 (show (roundTo 2 speedup) ++ "x")
      ++ padR 8 (if dmFound dm then "YES" else "NO")
      ++ padR 8 (show (dmLeftU dm))
      ++ show (dmRightU dm)
    ) [ (10,1), (14,1), (18,1), (20,1), (22,1), (24,1)
      , (10,2), (14,2), (18,2), (20,2), (22,2), (24,2)
      , (10,5), (14,5), (18,5), (20,5), (22,5), (24,5) ]

  putStrLn ""

  -- Part 4: Aliased double MITM (forced collisions)
  putStrLn "=== ALIASED DOUBLE MITM (forced collisions for sub-2^{n/2}) ==="
  putStrLn (padR 6 "n" ++ padR 6 "d" ++ padR 10 "aliasW" ++ padR 10 "normalW"
            ++ padR 10 "saving" ++ padR 8 "found" ++ padR 8 "aLeftU" ++ "aRightU")
  putStrLn (replicate 70 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        normal  = doubleMITM ws t
        aliased = aliasedDoubleMITM ws t
        saving = if dmTotalWork normal > 0
                 then 1.0 - fromIntegral (dmTotalWork aliased) / fromIntegral (dmTotalWork normal) :: Double
                 else 0
    putStrLn $ padR 6 (show n) ++ padR 6 (show (round d :: Int))
      ++ padR 10 (show (dmTotalWork aliased))
      ++ padR 10 (show (dmTotalWork normal))
      ++ padR 10 (show (roundTo 1 (saving * 100)) ++ "%")
      ++ padR 8 (if dmFound aliased then "YES" else "NO")
      ++ padR 8 (show (dmLeftU aliased))
      ++ show (dmRightU aliased)
    ) [ (10,1), (14,1), (18,1), (20,1)
      , (10,2), (14,2), (18,2), (20,2)
      , (10,5), (14,5), (18,5), (20,5) ]

  putStrLn ""

  -- Part 5: Various targets
  putStrLn "=== VARIOUS TARGETS n=20 d=1 ==="
  let (ws20, _) = mkDensity1 20
      total20 = sum ws20
  mapM_ (\(t, desc) -> do
    let dm = doubleMITM ws20 t
    putStrLn $ "  target=" ++ padR 10 desc
      ++ " found=" ++ padR 6 (show (dmFound dm))
      ++ " work=" ++ padR 8 (show (dmTotalWork dm))
      ++ " hits=" ++ show (dmHits dm)
    ) [ (total20 `div` 2, "sum/2")
      , (total20 `div` 2 + 1, "sum/2+1")
      , (total20 `div` 3, "sum/3")
      , (total20 `div` 5, "sum/5")
      , (0, "0")
      ]

  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"
