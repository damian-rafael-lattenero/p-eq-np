module Main where

import PeqNP.MultiLevelSieve

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " Multi-Level Group Sieve + Representations Benchmark"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: Standard multi-level
  putStrLn "--- MULTI-LEVEL GROUP SIEVE (no representations) ---"
  let results = map benchmark [8, 10, 12, 14, 16, 18, 20, 22, 24]
  putStr $ showBenchmark results
  putStrLn ""

  -- Part 2: With representations at merge
  putStrLn "--- WITH REPRESENTATIONS (modular filtered merge) ---"
  putStrLn "  n     rep_M4   rep_M8   4-way_4  4-way_8  MITM     best_ratio ok"
  putStrLn $ "  " ++ replicate 70 '-'

  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n
        mitm = 3 * 2 ^ (n `div` 2) :: Int
        sr_r4 = multiLevelRepSolve 2 4 ws t
        sr_r8 = multiLevelRepSolve 2 8 ws t
        sr_4w4 = fourWayRepSolve 4 4 ws t
        sr_4w8 = fourWayRepSolve 8 8 ws t
        works = [srWork sr_r4, srWork sr_r8, srWork sr_4w4, srWork sr_4w8]
        best = minimum works
        ratio = fromIntegral mitm / fromIntegral (max 1 best) :: Double
        allOk = all srCorrect [sr_r4, sr_r8, sr_4w4, sr_4w8]
    putStrLn $ "  " ++ padR 8 (show n)
      ++ padR 9 (show (srWork sr_r4))
      ++ padR 9 (show (srWork sr_r8))
      ++ padR 9 (show (srWork sr_4w4))
      ++ padR 9 (show (srWork sr_4w8))
      ++ padR 9 (show mitm)
      ++ padR 11 (show (roundTo 2 ratio))
      ++ (if allOk then "✓" else "✗")
    ) [8, 10, 12, 14, 16, 18, 20, 22, 24]

  putStrLn ""

  -- Part 3: Best of ALL methods
  putStrLn "--- BEST OF ALL METHODS ---"
  putStrLn "  n     2-level  4-way    rep      MITM     winner   ratio"
  putStrLn $ "  " ++ replicate 60 '-'

  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n
        mitm = 3 * 2 ^ (n `div` 2) :: Int
        w2 = srWork (multiLevelSolve 2 ws t)
        wr = srWork (multiLevelRepSolve 2 8 ws t)
        w4 = srWork (fourWayRepSolve 4 4 ws t)
        best = minimum [w2, wr, w4]
        winner | best == w2 = "2-level"
               | best == wr = "rep-M8"
               | otherwise  = "4-way"
        ratio = fromIntegral mitm / fromIntegral (max 1 best) :: Double
    putStrLn $ "  " ++ padR 8 (show n)
      ++ padR 9 (show w2)
      ++ padR 9 (show w4)
      ++ padR 9 (show wr)
      ++ padR 9 (show mitm)
      ++ padR 9 winner
      ++ show (roundTo 2 ratio)
    ) [8, 10, 12, 14, 16, 18, 20, 22, 24]

  putStrLn ""

  -- Effective exponent
  let (ws8, t8) = mkDensity1 8
      (ws24, t24) = mkDensity1 24
      w8 = minimum [srWork (multiLevelSolve 2 ws8 t8), srWork (fourWayRepSolve 4 4 ws8 t8)]
      w24 = minimum [srWork (multiLevelSolve 2 ws24 t24), srWork (fourWayRepSolve 4 4 ws24 t24)]
      expBest = logBase 2 (fromIntegral w24 / fromIntegral (max 1 w8)) / 16.0 * 2.0

  putStrLn $ "  Effective exponent (n=8→24): O(2^{" ++ show (roundTo 3 expBest) ++ "n})"
  putStrLn $ "  MITM:  O(2^{0.500n})"
  putStrLn $ "  BCJ:   O(2^{0.291n})"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"
