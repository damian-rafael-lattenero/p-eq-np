module Main where

{-
  TOPOLOGICAL QUOTIENT: the geometry of "near T" subsets

  Every subset S has a sum σ(S). We want to know if any σ(S) = T.

  Instead of looking at T specifically, look at the LANDSCAPE:
  how are subset sums DISTRIBUTED around T?

  If T is achievable: there's a "spike" at T (at least one subset hits it).
  If T is not achievable: there's a "gap" at T.

  THE QUESTION: can we detect the gap/spike without enumerating all 2^n subsets?

  Topological view: the subset sums form a POINT CLOUD on the integer line.
  The density of this cloud near T tells us about achievability.
  Density = number of subsets with sum in [T-δ, T+δ] / (2δ+1).

  For density-1:
    Total subsets = 2^n
    Range of sums ≈ n × 2^n
    Average density = 2^n / (n × 2^n) = 1/n

  So near T, we expect ~1/n subsets per integer position.
  If [x^T]P = 0: the density at T is 0 (but neighbors have ~1/n).
  If [x^T]P = 1: the density at T is 1 (same as neighbors).

  Can we compute the LOCAL DENSITY near T in O(n)?
  YES — via the saddle point variance! The saddle point gives
  the average density. But as we saw, it can't resolve individual positions.

  NEW IDEA: compute the SECOND-ORDER structure.
  The variance of the density fluctuations tells us about gaps.
  If there are systematic gaps → the fluctuation variance is high.
  If the sums are uniformly distributed → low fluctuation variance.

  Even newer: the NUMBER OF ACHIEVABLE SUMS in [T-δ, T+δ] is
  computable via the generating function evaluated at roots of unity
  of order 2δ+1. This needs only 2δ+1 evaluations!
  If δ = poly(n) → polynomial!

  The question: is a poly(n) window enough to detect if T itself is achievable?
-}

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (foldl', sort, group)
import Data.Bits (xor, shiftR, testBit)
import PeqNP.ActorSolver (padR)

-- | Compute the local density of subset sums around target T.
-- Returns: Map from (sum - T) → count, for sums in [T-δ, T+δ]
localDensity :: [Int] -> Int -> Int -> Map.Map Int Int
localDensity weights target delta =
  let n = length weights
      numSubsets = (2::Int)^n
      counts = foldl' (\acc mask ->
        let s = subsetSum mask weights
            offset = s - target
        in if abs offset <= delta
           then Map.insertWith (+) offset 1 acc
           else acc
        ) Map.empty [0..numSubsets-1]
  in counts
  where
    subsetSum mask ws = sum [w | (i,w) <- zip [0..] ws, testBit mask i]

-- | Compute density statistics around T
densityStats :: Map.Map Int Int -> Int -> (Double, Double, Int, Int, Bool)
  -- (avg_density, variance, count_at_T, total_in_window, T_is_achievable)
densityStats densityMap delta =
  let window = [(-delta)..delta]
      counts = [Map.findWithDefault 0 k densityMap | k <- window]
      windowSize = 2 * delta + 1
      total = sum counts
      avg = fromIntegral total / fromIntegral windowSize :: Double
      var = sum [(fromIntegral c - avg)^(2::Int) | c <- counts] / fromIntegral windowSize
      countAtT = Map.findWithDefault 0 0 densityMap
  in (avg, var, countAtT, total, countAtT > 0)

-- | The "gap signature": pattern of 0s and 1s around T.
-- For density-1: each position is 0 or 1 (unique sums).
-- The PATTERN of gaps might be detectable statistically.
gapSignature :: Map.Map Int Int -> Int -> [Int]
gapSignature densityMap delta =
  [Map.findWithDefault 0 k densityMap | k <- [(-delta)..delta]]

-- | Compute #(achievable sums in [T-δ, T+δ]) via generating function
-- at roots of unity of order (2δ+1).
-- P(ω^j) = ∏(1 + ω^{j·w_i}) for ω = exp(2πi/(2δ+1))
-- Then: #{sums ≡ T mod (2δ+1)} = (1/(2δ+1)) × Σ_j P(ω^j) × ω^{-jT}
--
-- This counts sums that are ≡ T mod (2δ+1), not exactly in [T-δ, T+δ].
-- But if 2δ+1 > range of sums, it's exact!
-- For 2δ+1 = polynomial: it counts aliased sums (mod 2δ+1).
countViaDFT :: [Int] -> Int -> Int -> Double
countViaDFT weights target delta =
  let m = 2 * delta + 1
      omega_r j = 2 * pi * fromIntegral j / fromIntegral m :: Double
      -- P(ω^j) = ∏(1 + exp(i·j·w_k·2π/m))
      -- We need the REAL part of (1/m) Σ_j P(ω^j) × exp(-i·j·T·2π/m)
      result = foldl' (\(reAcc, imAcc) j ->
        let (reProd, imProd) = foldl' (\(ra, ia) w ->
              let angle = omega_r j * fromIntegral w
                  re1 = 1 + cos angle
                  im1 = sin angle
              in (ra * re1 - ia * im1, ra * im1 + ia * re1)
              ) (1, 0) weights
            -- Multiply by ω^{-jT}
            phaseAngle = -(omega_r j * fromIntegral target)
            rePhase = cos phaseAngle
            imPhase = sin phaseAngle
            reTerm = reProd * rePhase - imProd * imPhase
        in (reAcc + reTerm, imAcc)
        ) (0, 0) [0..m-1]
  in fst result / fromIntegral m

mkHash :: Int -> ([Int], Int)
mkHash n =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
           | i <- [0..n-1 :: Int]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

dpReachable :: [Int] -> Set.Set Int
dpReachable = foldl' (\acc w -> Set.union acc (Set.map (+w) acc)) (Set.singleton 0)

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " TOPOLOGICAL QUOTIENT: the geometry near T"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: What does the landscape look like around T?
  let n = 12
      (ws, tNo) = mkHash n
      tYes = sum (take (n `div` 2) ws)
      delta = 20

  putStrLn $ "n=" ++ show n ++ ", delta=" ++ show delta
  putStrLn ""

  -- NO target landscape
  let dMapNo = localDensity ws tNo delta
      (avgNo, varNo, ctNo, totalNo, _) = densityStats dMapNo delta
      sigNo = gapSignature dMapNo delta
  putStrLn "=== LANDSCAPE around NO target ==="
  putStrLn $ "  avg density: " ++ showF 3 avgNo ++ " subsets/position"
  putStrLn $ "  variance:    " ++ showF 3 varNo
  putStrLn $ "  count at T:  " ++ show ctNo ++ " (should be 0)"
  putStrLn $ "  total in window: " ++ show totalNo
  putStrLn $ "  pattern: " ++ concatMap (\c -> if c > 0 then "#" else ".") sigNo
  putStrLn ""

  -- YES target landscape
  let dMapYes = localDensity ws tYes delta
      (avgYes, varYes, ctYes, totalYes, _) = densityStats dMapYes delta
      sigYes = gapSignature dMapYes delta
  putStrLn "=== LANDSCAPE around YES target ==="
  putStrLn $ "  avg density: " ++ showF 3 avgYes ++ " subsets/position"
  putStrLn $ "  variance:    " ++ showF 3 varYes
  putStrLn $ "  count at T:  " ++ show ctYes ++ " (should be ≥1)"
  putStrLn $ "  total in window: " ++ show totalYes
  putStrLn $ "  pattern: " ++ concatMap (\c -> if c > 0 then "#" else ".") sigYes
  putStrLn ""

  -- Part 2: Can DFT with small window detect achievability?
  putStrLn "=== DFT WINDOW: count sums ≡ T mod (2δ+1) ==="
  putStrLn (padR 8 "delta" ++ padR 14 "DFT(NO)" ++ padR 14 "DFT(YES)"
    ++ padR 10 "evals" ++ padR 12 "separable?")
  putStrLn (replicate 58 '-')
  mapM_ (\d -> do
    let dftNo = countViaDFT ws tNo d
        dftYes = countViaDFT ws tYes d
        m = 2 * d + 1
    putStrLn $ padR 8 (show d)
      ++ padR 14 (showF 2 dftNo)
      ++ padR 14 (showF 2 dftYes)
      ++ padR 10 (show m)
      ++ padR 12 (if abs (dftYes - dftNo) > 0.5 then "YES!" else "no")
    ) [1, 2, 5, 10, 20, 50, 100, 200, 500]
  putStrLn ""

  -- Part 3: The statistical test — is the gap pattern distinguishable?
  putStrLn "=== STATISTICAL TEST: can we tell NO from YES? ==="
  putStrLn "  Hypothesis: NO targets have avg density ~1/n at T,"
  putStrLn "  but the specific position T has count 0."
  putStrLn "  If the neighborhood density is significantly different"
  putStrLn "  between YES and NO → detectable without solving."
  putStrLn ""

  -- Test many targets
  let dpSet = dpReachable ws
      allTargets = [tNo - 50 .. tNo + 50]
      results = [(t, Set.member t dpSet,
                  let dm = localDensity ws t 5
                      (a, v, c, _, _) = densityStats dm 5
                  in (a, v, c))
                | t <- allTargets]
      yesTargets = [(a, v) | (_, True, (a, v, _)) <- results]
      noTargets  = [(a, v) | (_, False, (a, v, _)) <- results]
      avgYesD = if null yesTargets then 0 else sum (map fst yesTargets) / fromIntegral (length yesTargets)
      avgNoD  = if null noTargets then 0 else sum (map fst noTargets) / fromIntegral (length noTargets)
      avgYesV = if null yesTargets then 0 else sum (map snd yesTargets) / fromIntegral (length yesTargets)
      avgNoV  = if null noTargets then 0 else sum (map snd noTargets) / fromIntegral (length noTargets)

  putStrLn $ "  YES targets (" ++ show (length yesTargets) ++ "):"
    ++ " avg_density=" ++ showF 3 avgYesD
    ++ " avg_variance=" ++ showF 3 avgYesV
  putStrLn $ "  NO targets  (" ++ show (length noTargets) ++ "):"
    ++ " avg_density=" ++ showF 3 avgNoD
    ++ " avg_variance=" ++ showF 3 avgNoV
  putStrLn $ "  Density difference: " ++ showF 4 (avgYesD - avgNoD)
  putStrLn $ "  Variance difference: " ++ showF 4 (avgYesV - avgNoV)
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"

showF :: Int -> Double -> String
showF decimals x
  | isNaN x = "NaN"
  | isInfinite x = if x > 0 then "+Inf" else "-Inf"
  | otherwise =
      let factor = 10.0 ^^ decimals :: Double
          rounded = fromIntegral (round (x * factor) :: Integer) / factor
      in show rounded
