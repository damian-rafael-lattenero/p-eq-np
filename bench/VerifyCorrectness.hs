module Main where

import PeqNP.MultiLevelSieve
import qualified Data.Set as Set

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " CORRECTNESS VERIFICATION: all methods vs brute force DP"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: Verify 4-way gives correct answers for MANY targets per n
  putStrLn "--- PART 1: 4-way vs DP, multiple targets per n ---"
  putStrLn "n     targets_tested  all_correct  false_pos  false_neg"
  putStrLn (replicate 60 '-')

  mapM_ verifyN [8, 10, 12, 14, 16]

  putStrLn ""

  -- Part 2: Verify work metric is honest
  putStrLn "--- PART 2: work breakdown (is 4n honest?) ---"
  putStrLn "n     4way_work  perQ_bf  merge_est  sum_weights  DP_size"
  putStrLn (replicate 60 '-')

  mapM_ workBreakdown [8, 10, 12, 14, 16, 18, 20]

  putStrLn ""

  -- Part 3: Specific hard instances
  putStrLn "--- PART 3: hard instances (NO answers at density 1) ---"
  putStrLn ""

  mapM_ verifyHard
    [ ([502,757,1018,543,876,691,1234,419,800,663], 3775, "deadzone_NO")
    , ([502,757,1018,543,876,691,1234,419,800,663], 4200, "deadzone_YES")
    , ([37,41,43,47,53,59], 150, "primes_NO")
    , ([37,41,43,47,53,59], 137, "primes_YES")
    ]

-- | Verify 4-way against DP for many targets
verifyN :: Int -> IO ()
verifyN n = do
  let (ws, _) = mkDensity1 n
      dpSums = bruteForceDP ws
      dpSize = Set.size dpSums
      totalSum = sum ws
      -- Test YES targets (known reachable)
      yesTargets = take 10 (Set.toList dpSums)
      -- Test NO targets
      noTargets = take 10 [t | t <- [1..totalSum], not (Set.member t dpSums)]
      allTargets = yesTargets ++ noTargets
      -- Run 4-way on each
      results = [ (t, dpAns, ourAns)
                | t <- allTargets
                , let dpAns = Set.member t dpSums
                      sr = fourWayRepSolve 4 4 ws t
                      ourAns = srFound sr
                ]
      falsePos = length [() | (_, False, True) <- results]
      falseNeg = length [() | (_, True, False) <- results]
      allOk = falsePos == 0 && falseNeg == 0
  putStrLn $ padR 6 (show n)
    ++ padR 16 (show (length allTargets))
    ++ padR 13 (if allOk then "✓ ALL OK" else "✗ ERRORS")
    ++ padR 11 (show falsePos)
    ++ show falseNeg

-- | Show work breakdown to verify what's counted
workBreakdown :: Int -> IO ()
workBreakdown n = do
  let (ws, t) = mkDensity1 n
      sr = fourWayRepSolve 4 4 ws t
      q = n `div` 4
      -- Per quarter brute force: 2^{n/4}
      perQBF = 4 * (2 ^ q)
      -- Merge estimate: |left| + |right|
      mergeEst = srLeftSize sr + srRightSize sr
      totalSum = sum ws
      dpSize = Set.size (bruteForceDP ws)
  putStrLn $ padR 6 (show n)
    ++ padR 11 (show (srWork sr))
    ++ padR 9 (show perQBF)
    ++ padR 11 (show mergeEst)
    ++ padR 13 (show totalSum)
    ++ show dpSize

-- | Verify specific hard instance
verifyHard :: ([Int], Int, String) -> IO ()
verifyHard (ws, t, label) = do
  let dpSums = bruteForceDP ws
      dpAns = Set.member t dpSums
      sr4 = fourWayRepSolve 4 4 ws t
      sr2 = multiLevelSolve 2 ws t
      sr1 = multiLevelSolve 1 ws t
  putStrLn $ "  " ++ padR 15 label
    ++ " DP=" ++ padR 6 (show dpAns)
    ++ " 1-level=" ++ padR 6 (show (srFound sr1))
    ++ " 2-level=" ++ padR 6 (show (srFound sr2))
    ++ " 4-way=" ++ padR 6 (show (srFound sr4))
    ++ (if srFound sr4 == dpAns then "✓" else "✗ MISMATCH!")

-- Reuse bruteForceDP from module
bruteForceDP :: [Int] -> Set.Set Int
bruteForceDP = foldl (\s w -> Set.union s (Set.map (+w) s)) (Set.singleton 0)
