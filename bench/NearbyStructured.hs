module Main where

{-
  NEARBY STRUCTURED INSTANCE + CORRECTION

  hard = easy + delta

  If we can find a structured instance S "close" to the hard instance H,
  solve S in polynomial time, and the correction delta is small enough
  to handle in polynomial time → we win.

  Structured instances we can solve fast:
  1. Arithmetic progression: w_i = a + b·i → O(n³) via index DP
  2. Geometric/powers: w_i = c^i → special structure
  3. Low-entropy: all weights nearly equal → few distinct sums → O(n²)

  For each: fit the weights, measure the residuals, check if
  the correction problem is tractable.
-}

import Data.List (foldl', minimumBy, sortBy)
import Data.Ord (comparing)
import Data.Bits (xor, shiftR, testBit)
import qualified Data.Set as Set
import PeqNP.ActorSolver (padR)

-- | Fit weights to best arithmetic progression: w_i ≈ a + b·i
-- Uses least-squares fit: a = mean(w) - b·mean(i), b = cov(w,i)/var(i)
fitAP :: [Int] -> (Double, Double, [Int])  -- (a, b, deltas)
fitAP ws =
  let n = length ws
      fn = fromIntegral n :: Double
      is = [0..n-1]
      meanI = fromIntegral (sum is) / fn
      meanW = fromIntegral (sum ws) / fn
      covIW = sum [fromIntegral i * fromIntegral w | (i,w) <- zip is ws] / fn - meanI * meanW
      varI  = sum [fromIntegral i * fromIntegral i | i <- is] / fn - meanI * meanI
      b = covIW / varI
      a = meanW - b * meanI
      predicted = [round (a + b * fromIntegral i) :: Int | i <- is]
      deltas = zipWith (-) ws predicted
  in (a, b, deltas)

-- | Fit weights to best constant: w_i ≈ c (simplest structure)
fitConst :: [Int] -> (Int, [Int])  -- (c, deltas)
fitConst ws =
  let c = sum ws `div` length ws
  in (c, map (\w -> w - c) ws)

-- | Fit weights to nearest "round" multiples: w_i ≈ round(w_i/M) × M
fitRound :: Int -> [Int] -> ([Int], [Int])  -- (structured, deltas)
fitRound m ws =
  let structured = [((w + m `div` 2) `div` m) * m | w <- ws]
      deltas = zipWith (-) ws structured
  in (structured, deltas)

-- | Given deltas, can the correction problem be solved in poly time?
-- The correction is: Σ x_i d_i = D for some specific D.
-- If max|d_i| = O(poly(n)), DP solves this in O(n · max|d_i|).
-- Measure: max|d_i|, range of possible Σ x_i d_i
deltaStats :: [Int] -> (Int, Int, Int, Int)  -- (maxAbs, minSum, maxSum, range)
deltaStats ds =
  let maxAbs = maximum (map abs ds)
      posSum = sum [d | d <- ds, d > 0]
      negSum = sum [d | d <- ds, d < 0]
  in (maxAbs, negSum, posSum, posSum - negSum)

-- | Actually check: does the split approach find the right answer?
-- 1. Solve structured part for all feasible targets T'
-- 2. For each solution, check if correction matches
splitSolve :: [Int] -> [Int] -> Int -> (Bool, Int, Int)
  -- Returns (found, structured_solutions_checked, total_work)
splitSolve structured deltas target =
  let -- All reachable sums of structured part
      structSums = foldl' (\acc w -> Set.union acc (Set.map (+w) acc))
                          (Set.singleton 0) structured
      -- For each structured sum s: need correction d = target - s
      -- Check if d is reachable by deltas
      deltaSums = foldl' (\acc d -> Set.union acc (Set.map (+d) acc))
                         (Set.singleton 0) deltas
      -- Count matches
      matches = length [s | s <- Set.toList structSums,
                            Set.member (target - s) deltaSums]
  in (matches > 0, Set.size structSums, Set.size structSums + Set.size deltaSums)

mkHash :: Int -> ([Int], Int)
mkHash n =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
           | i <- [0..n-1 :: Int]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " NEARBY STRUCTURED + CORRECTION: hard = easy + delta"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  let n = 14
      (ws, t) = mkHash n
  putStrLn $ "Instance: HASH n=" ++ show n ++ ", target=" ++ show t
  putStrLn $ "  weights = " ++ show (take 5 ws) ++ "..."
  putStrLn ""

  -- Fit 1: Arithmetic progression
  let (a, b, deltasAP) = fitAP ws
      (maxD, minS, maxS, range) = deltaStats deltasAP
  putStrLn "=== FIT 1: Arithmetic Progression ==="
  putStrLn $ "  Best fit: w_i ≈ " ++ show (round a :: Int) ++ " + " ++ show (round b :: Int) ++ "·i"
  putStrLn $ "  Deltas: " ++ show (take 7 deltasAP) ++ "..."
  putStrLn $ "  max|delta| = " ++ show maxD
  putStrLn $ "  Delta sum range: [" ++ show minS ++ ", " ++ show maxS ++ "]"
  putStrLn $ "  Range width: " ++ show range
  putStrLn $ "  For poly DP on deltas: need max|d| = O(poly(n)) = O(" ++ show (n^3) ++ ")"
  putStrLn $ "  Actual max|d| = " ++ show maxD
    ++ (if maxD <= n^3 then " ← POLYNOMIAL! DP works!" else " ← EXPONENTIAL. DP explodes.")
  putStrLn ""

  -- Fit 2: Round to multiples of M
  putStrLn "=== FIT 2: Round to multiples of M ==="
  putStrLn (padR 10 "M" ++ padR 14 "max|delta|" ++ padR 14 "poly-bound"
    ++ padR 14 "tractable?" ++ padR 14 "struct-sums")
  putStrLn (replicate 66 '-')
  mapM_ (\m -> do
    let (structured, deltas) = fitRound m ws
        (maxDelta, _, _, _) = deltaStats deltas
        polyBound = n * n * n  -- n^3
        -- How many distinct structured sums?
        structDistinct = Set.size $ foldl' (\acc w -> Set.union acc (Set.map (+w) acc))
                           (Set.singleton 0) structured
    putStrLn $ padR 10 (show m)
      ++ padR 14 (show maxDelta)
      ++ padR 14 (show polyBound)
      ++ padR 14 (if maxDelta <= polyBound then "YES" else "no")
      ++ padR 14 (show structDistinct)
    ) [2, 4, 8, 16, 64, 256, 1024, 4096]
  putStrLn ""

  -- Fit 3: Constant approximation
  let (c, deltasConst) = fitConst ws
      (maxDC, _, _, rangeC) = deltaStats deltasConst
  putStrLn "=== FIT 3: Constant approximation ==="
  putStrLn $ "  Best constant: " ++ show c
  putStrLn $ "  max|delta| = " ++ show maxDC ++ ", range = " ++ show rangeC
  putStrLn $ "  Structured part: Σ x_i·c = c·k (just choose k = T/c)"
  putStrLn $ "  Correction: Σ x_i·d_i = T - c·k for the right k"
  putStrLn $ "  max|delta| tractable? " ++ show maxDC ++ " vs n^3=" ++ show (n^3)
    ++ ": " ++ (if maxDC <= n^3 then "YES" else "NO")
  putStrLn ""

  -- THE KEY QUESTION: as n grows, does max|delta| grow polynomially or exponentially?
  putStrLn "=== SCALING: max|delta| for AP fit as n grows ==="
  putStrLn (padR 5 "n" ++ padR 14 "max|delta|" ++ padR 14 "2^(n-1)"
    ++ padR 14 "delta/2^n" ++ padR 14 "delta/n^3")
  putStrLn (replicate 62 '-')
  mapM_ (\ni -> do
    let (wsi, _) = mkHash ni
        (_, _, deltasi) = fitAP wsi
        (maxDi, _, _, _) = deltaStats deltasi
        ratio2n = fromIntegral maxDi / (2 ** fromIntegral (ni-1)) :: Double
        ration3 = fromIntegral maxDi / fromIntegral (ni^(3::Int)) :: Double
    putStrLn $ padR 5 (show ni)
      ++ padR 14 (show maxDi)
      ++ padR 14 (show ((2::Int)^(ni-1)))
      ++ padR 14 (showF 3 ratio2n)
      ++ padR 14 (showF 1 ration3)
    ) [8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn "If delta/n^3 stays BOUNDED → poly-time correction → P = NP"
  putStrLn "If delta/2^n stays BOUNDED → correction is O(weight) → same as original"
  putStrLn "═══════════════════════════════════════════════════════════"

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int) / fromIntegral factor :: Double
  in show rounded
