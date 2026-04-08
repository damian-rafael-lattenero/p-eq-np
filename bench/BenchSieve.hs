module Main where

import PeqNP.MultiLevelSieve

roundTo :: Int -> Double -> Double
roundTo n x = fromIntegral (round (x * 10 ^ n) :: Int) / 10 ^ (fromIntegral n)

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " Multi-Level Group Sieve Benchmark (density 1)"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Benchmark across n values
  let results = map benchmark [8, 10, 12, 14, 16, 18, 20, 22, 24]
  putStr $ showBenchmark results

  putStrLn ""
  putStrLn "  Growth analysis (best vs MITM):"
  putStrLn ""

  let pairs = zip results (tail results)
  mapM_ (\(r1, r2) -> do
    let n1 = brN r1; n2 = brN r2
        g_best = fromIntegral (brBest r2) / fromIntegral (max 1 (brBest r1)) :: Double
        g_mitm = fromIntegral (brMITM r2) / fromIntegral (max 1 (brMITM r1)) :: Double
    putStrLn $ "  n=" ++ show n1 ++ "→" ++ show n2
      ++ ": best×" ++ show (roundTo 2 g_best)
      ++ " MITM×" ++ show (roundTo 2 g_mitm)
    ) pairs

  putStrLn ""

  -- Compute effective exponents
  let firstR = head results
      lastR = last results
      n1 = fromIntegral (brN firstR) :: Double
      n2 = fromIntegral (brN lastR) :: Double
      expBest = logBase 2 (fromIntegral (brBest lastR) / fromIntegral (max 1 (brBest firstR))) / (n2 - n1) * 2
      expMITM = logBase 2 (fromIntegral (brMITM lastR) / fromIntegral (max 1 (brMITM firstR))) / (n2 - n1) * 2

  putStrLn $ "  Effective exponents (n=" ++ show (brN firstR) ++ "→" ++ show (brN lastR) ++ "):"
  putStrLn $ "    Best group sieve: O(2^{" ++ show (roundTo 3 expBest) ++ "n})"
  putStrLn $ "    MITM:             O(2^{" ++ show (roundTo 3 expMITM) ++ "n})"
  putStrLn $ "    BCJ (reference):  O(2^{0.291n})"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"
