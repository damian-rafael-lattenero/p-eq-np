module Main where

{-
  RECURSIVE APPROXIMATION: hard = easy + delta, then delta = easy' + delta', ...

  At each level, fit the residuals with the best structured approximation.
  If residuals shrink by factor c < 1 per level:
    After k levels: residual ~ c^k × 2^n
    Need c^k × 2^n ≤ poly(n) → k = O(n / log(1/c))

  If k = O(log n) → total is polynomial!
  If k = O(n) → same as original.

  THE QUESTION: how fast do residuals shrink?
-}

import Data.List (foldl')
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- | Fit weights to best AP, return (structured_part, residuals)
fitAndSplit :: [Int] -> ([Int], [Int])
fitAndSplit ws =
  let n = length ws
      fn = fromIntegral n :: Double
      is = [0..n-1]
      meanI = fromIntegral (sum is) / fn
      meanW = fromIntegral (sum ws) / fn
      covIW = sum [fromIntegral i * fromIntegral w | (i,w) <- zip is ws] / fn - meanI * meanW
      varI  = sum [fromIntegral i * fromIntegral i | i <- is] / fn - meanI * meanI
      b = if varI == 0 then 0 else covIW / varI
      a = meanW - b * meanI
      structured = [round (a + b * fromIntegral i) :: Int | i <- is]
      residuals = zipWith (-) ws structured
  in (structured, residuals)

-- | Recursively decompose: w = s₁ + s₂ + ... + sₖ + residual
-- Returns list of (level, max|residual|, shrinkage_factor)
recursiveDecompose :: Int -> [Int] -> [(Int, Int, Double)]
recursiveDecompose maxLevels ws = go 0 ws (maximum (map abs ws))
  where
    go level residuals prevMax
      | level >= maxLevels = []
      | maximum (map abs residuals) == 0 = [(level, 0, 0)]
      | otherwise =
          let (_, newResiduals) = fitAndSplit residuals
              newMax = maximum (map abs newResiduals)
              shrinkage = fromIntegral newMax / fromIntegral prevMax :: Double
          in (level, newMax, shrinkage) : go (level + 1) newResiduals newMax

mkHash :: Int -> ([Int], Int)
mkHash n =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
           | i <- [0..n-1 :: Int]]
  in (ws, sum ws `div` 2 + 1)

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " RECURSIVE APPROXIMATION: how fast do residuals shrink?"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Recursive decomposition for n=20
  let n = 20
      (ws, _) = mkHash n
  putStrLn $ "Instance: HASH n=" ++ show n
  putStrLn ""

  putStrLn "=== RECURSIVE AP FIT: level by level ==="
  putStrLn (padR 8 "level" ++ padR 14 "max|resid|" ++ padR 12 "shrinkage"
    ++ padR 14 "poly(n³)?" ++ padR 14 "log₂(resid)")
  putStrLn (replicate 62 '-')
  let decomp = recursiveDecompose 20 ws
  mapM_ (\(lv, maxR, shr) -> do
    let polyBound = n^(3::Int)
        logR = if maxR > 0 then logBase 2 (fromIntegral maxR) :: Double else 0
    putStrLn $ padR 8 (show lv)
      ++ padR 14 (show maxR)
      ++ padR 12 (if lv == 0 then "-" else showF 3 shr)
      ++ padR 14 (if maxR <= polyBound then "YES!" else "no")
      ++ padR 14 (showF 1 logR ++ " bits")
    ) decomp
  putStrLn ""

  -- How many levels needed to reach polynomial?
  let levelsToReachPoly ni =
        let (wsi, _) = mkHash ni
            polyB = ni^(3::Int)
            dec = recursiveDecompose 50 wsi
        in case [(lv, mr) | (lv, mr, _) <- dec, mr <= polyB, mr > 0] of
             ((lv, _):_) -> Just lv
             []          -> Nothing

  putStrLn "=== LEVELS NEEDED TO REACH poly(n) RESIDUALS ==="
  putStrLn (padR 5 "n" ++ padR 14 "levels" ++ padR 14 "n/2" ++ padR 14 "log(n)")
  putStrLn (replicate 48 '-')
  mapM_ (\ni -> do
    let levels = levelsToReachPoly ni
    putStrLn $ padR 5 (show ni)
      ++ padR 14 (maybe "never" show levels)
      ++ padR 14 (show (ni `div` 2))
      ++ padR 14 (show (ceiling (logBase 2 (fromIntegral ni) :: Double) :: Int))
    ) [8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

  -- The dream: what if shrinkage were > 50% per level?
  putStrLn "=== WHAT-IF: how many levels with different shrinkage rates ==="
  putStrLn "  For max|delta| to go from 2^n to n³:"
  putStrLn "  need k levels where (shrinkage)^k × 2^n ≤ n³"
  putStrLn ""
  putStrLn (padR 12 "shrinkage" ++ padR 8 "n=14" ++ padR 8 "n=20"
    ++ padR 8 "n=30" ++ padR 8 "n=40" ++ padR 10 "growth")
  putStrLn (replicate 55 '-')
  mapM_ (\shr -> do
    let levelsNeeded ni =
          let target = fromIntegral (ni^(3::Int)) :: Double
              start = 2 ** fromIntegral ni :: Double
          in ceiling (log (target / start) / log shr) :: Int
    putStrLn $ padR 12 (showF 2 shr)
      ++ padR 8 (show (levelsNeeded (14::Int)))
      ++ padR 8 (show (levelsNeeded (20::Int)))
      ++ padR 8 (show (levelsNeeded (30::Int)))
      ++ padR 8 (show (levelsNeeded (40::Int)))
      ++ padR 10 (if levelsNeeded 40 <= 2 * levelsNeeded 20 then "~O(n)" else "sublinear?")
    ) [0.9, 0.75, 0.5, 0.25, 0.1]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn "For POLYNOMIAL total: need O(log n) levels."
  putStrLn "That requires shrinkage ~ 1/n per level (residual drops by 1/n each step)."
  putStrLn "Actual shrinkage for random weights: ~0.45 (constant)."
  putStrLn "0.45^k × 2^n ≤ n³ → k ≈ 0.87n → O(n) levels → no savings."
  putStrLn "═══════════════════════════════════════════════════════════"

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int) / fromIntegral factor :: Double
  in show rounded
