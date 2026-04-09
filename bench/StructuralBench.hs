module Main where

import PeqNP.StructuralSolver
import PeqNP.ActorSolver (mkDensity1, mkDensityD, padR, roundTo)
import PeqNP.MultiLevelSieve (recursiveRepSolveRaw)
import PeqNP.OracleSolver (oraclePrecheck)
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

  -- Part 6: v2 on-the-fly comparison
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " ON-THE-FLY v2: half-enum + 4 match types + early exit"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "=== v1 vs v2 WORK COMPARISON ==="
  putStrLn (padR 5 "n" ++ padR 4 "d" ++ padR 10 "v1work" ++ padR 10 "v2enum"
            ++ padR 10 "v2early" ++ padR 9 "speedup" ++ padR 6 "ok?" ++ "match")
  putStrLn (replicate 65 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        v1 = doubleMITM ws t
        v2 = solve ws t
        v2ok = case solSolution v2 of
          Just sol -> sum sol == t
          Nothing  -> not (dmFound v1)
        speedup = if solTotalEnum v2 > 0
                  then fromIntegral (dmTotalWork v1) / fromIntegral (solTotalEnum v2)
                  else 0 :: Double
    putStrLn $ padR 5 (show n) ++ padR 4 (show (round d :: Int))
      ++ padR 10 (show (dmTotalWork v1))
      ++ padR 10 (show (solTotalEnum v2))
      ++ padR 10 (show (solWorkDone v2))
      ++ padR 9 (show (roundTo 2 speedup) ++ "x")
      ++ padR 6 (if v2ok then "OK" else "BUG")
      ++ maybe "none" show (solMatchType v2)
    ) [ (10,1), (14,1), (18,1), (20,1), (24,1), (28,1)
      , (10,2), (14,2), (18,2), (20,2), (24,2), (28,2)
      , (10,5), (14,5), (18,5), (20,5), (24,5), (28,5) ]

  putStrLn ""

  -- Part 7: Timing comparison at larger n
  putStrLn "=== TIMING: v1 vs v2 (density-1) ==="
  putStrLn (padR 5 "n" ++ padR 12 "v1_ms" ++ padR 12 "v2_ms"
            ++ padR 10 "speedup" ++ padR 8 "found" ++ "match")
  putStrLn (replicate 55 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n
    t0 <- getCPUTime
    let !v1 = dmFound (doubleMITM ws t)
    t1 <- getCPUTime
    let !v2r = solve ws t
        !v2 = solFound v2r
    t2 <- getCPUTime
    let ms1 = fromIntegral (t1 - t0) / 1e9 :: Double
        ms2 = fromIntegral (t2 - t1) / 1e9 :: Double
        spd = if ms2 > 0.01 then ms1 / ms2 else 0
    putStrLn $ padR 5 (show n)
      ++ padR 12 (printf "%.1f" ms1)
      ++ padR 12 (printf "%.1f" ms2)
      ++ padR 10 (if spd > 0 then printf "%.1fx" spd else "n/a")
      ++ padR 8 (if v2 then "YES" else "NO")
      ++ maybe "none" show (solMatchType v2r)
    ) [20, 22, 24, 26, 28, 30, 32, 34, 36]

  putStrLn ""

  -- Part 8: Oracle + v2 combo
  putStrLn "=== ORACLE + v2 COMBO ==="
  putStrLn (padR 5 "n" ++ padR 4 "d" ++ padR 10 "v2work" ++ padR 12 "oracle"
            ++ padR 8 "found" ++ "match")
  putStrLn (replicate 50 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        oCheck = oraclePrecheck ws t
        v2 = case oCheck of
               Just False -> SolveResult False Nothing Nothing 0 0 0 0
               _          -> solve ws t
        oracleStr = case oCheck of
          Just False -> "PRUNED"
          _          -> "pass"
    putStrLn $ padR 5 (show n) ++ padR 4 (show (round d :: Int))
      ++ padR 10 (show (solTotalEnum v2))
      ++ padR 12 oracleStr
      ++ padR 8 (if solFound v2 then "YES" else "NO")
      ++ maybe "none" show (solMatchType v2)
    ) [ (14,1), (18,1), (22,1), (26,1), (30,1)
      , (14,2), (18,2), (22,2), (26,2), (30,2)
      , (14,5), (18,5), (22,5), (26,5), (30,5) ]

  putStrLn ""

  -- Part 9: v3 column-by-column vs v2 element-by-element
  putStrLn "=== v3 COLUMN-BY-COLUMN vs v2 ELEMENT-BY-ELEMENT ==="
  putStrLn (padR 5 "n" ++ padR 4 "d" ++ padR 10 "v2enum" ++ padR 10 "v3enum"
            ++ padR 10 "v2early" ++ padR 10 "v3early" ++ padR 6 "ok?" ++ "v3match")
  putStrLn (replicate 65 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        v2 = solve ws t
        v3 = doubleMITMv3 ws t
        v3ok = case solSolution v3 of
          Just sol -> sum sol == t
          Nothing  -> not (solFound v2)
    putStrLn $ padR 5 (show n) ++ padR 4 (show (round d :: Int))
      ++ padR 10 (show (solTotalEnum v2))
      ++ padR 10 (show (solTotalEnum v3))
      ++ padR 10 (show (solWorkDone v2))
      ++ padR 10 (show (solWorkDone v3))
      ++ padR 6 (if v3ok then "OK" else "BUG")
      ++ maybe "none" show (solMatchType v3)
    ) [ (10,1), (14,1), (18,1), (20,1), (24,1)
      , (10,2), (14,2), (18,2), (20,2), (24,2)
      , (10,5), (14,5), (18,5), (20,5), (24,5) ]

  putStrLn ""

  -- Part 10: v3 timing comparison
  putStrLn "=== TIMING: v2 vs v3 (density-1) ==="
  putStrLn (padR 5 "n" ++ padR 12 "v2_ms" ++ padR 12 "v3_ms"
            ++ padR 10 "ratio" ++ padR 8 "found" ++ "match")
  putStrLn (replicate 55 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n
    t0 <- getCPUTime
    let !v2r = solve ws t
        !v2 = solFound v2r
    t1 <- getCPUTime
    let !v3r = doubleMITMv3 ws t
        !v3 = solFound v3r
    t2 <- getCPUTime
    let ms2 = fromIntegral (t1 - t0) / 1e9 :: Double
        ms3 = fromIntegral (t2 - t1) / 1e9 :: Double
        ratio = if ms3 > 0.01 then ms2 / ms3 else 0
    putStrLn $ padR 5 (show n)
      ++ padR 12 (printf "%.1f" ms2)
      ++ padR 12 (printf "%.1f" ms3)
      ++ padR 10 (if ratio > 0 then printf "%.2fx" ratio else "n/a")
      ++ padR 8 (if v3 then "YES" else "NO")
      ++ maybe "none" show (solMatchType v3r)
    ) [14, 18, 20, 24, 28, 30, 32]

  putStrLn ""

  -- Part 11: v3 on structured instances (high density — many collisions)
  putStrLn "=== v3 on STRUCTURED instances (collision-rich) ==="
  putStrLn (padR 5 "n" ++ padR 4 "d" ++ padR 10 "v2enum" ++ padR 10 "v3enum"
            ++ padR 10 "ratio" ++ padR 8 "found")
  putStrLn (replicate 55 '-')
  mapM_ (\(n, d) -> do
    let (ws, t) = mkDensityD n d
        v2 = solve ws t
        v3 = doubleMITMv3 ws t
        ratio = if solTotalEnum v3 > 0
                then fromIntegral (solTotalEnum v2) / fromIntegral (solTotalEnum v3) :: Double
                else 0
    putStrLn $ padR 5 (show n) ++ padR 4 (show (round d :: Int))
      ++ padR 10 (show (solTotalEnum v2))
      ++ padR 10 (show (solTotalEnum v3))
      ++ padR 10 (printf "%.2fx" ratio)
      ++ padR 8 (if solFound v3 then "YES" else "NO")
    ) [ (20,3), (24,3), (28,3), (20,5), (24,5), (28,5)
      , (20,8), (24,8), (28,8), (20,10), (24,10), (28,10) ]

  putStrLn ""

  -- Part 12: Half-enumeration savings detail (column vs element enumerator)
  putStrLn "=== ENUMERATOR COMPARISON: element-by-element vs column-by-column ==="
  putStrLn (padR 5 "n" ++ padR 10 "elemU" ++ padR 10 "colU"
            ++ padR 8 "same?" ++ padR 10 "halfSize")
  putStrLn (replicate 45 '-')
  mapM_ (\n -> do
    let (ws, _) = mkDensity1 n
        mid = n `div` 2
        halfSize = max 1 (n `div` 4)
        leftW = take mid ws
        elemNode = enumerateHalf halfSize leftW
        colNode  = enumerateColumns halfSize leftW
        elemU = pnUniqueCount elemNode
        colU  = pnUniqueCount colNode
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show elemU)
      ++ padR 10 (show colU)
      ++ padR 8 (if elemU == colU then "YES" else "NO")
      ++ padR 10 (show halfSize)
    ) [10, 14, 18, 20, 24, 28, 30, 32]

  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"
