module Main where

{-
  SADDLE POINT METHOD: extract [x^T]P(x) in O(n) via complex analysis

  By Cauchy's integral formula:
    [x^T]P(x) = (1/2πi) ∮ P(z)/z^{T+1} dz

  The saddle point z₀ minimizes |P(z)/z^{T+1}| on the positive real axis:
    z₀ satisfies: T = z₀ × P'(z₀)/P(z₀) = Σ w_i z₀^{w_i} / (1 + z₀^{w_i})

  Gaussian approximation around z₀:
    [x^T]P ≈ P(z₀) / (z₀^T × √(2π × V))
  where V = z₀² × (d²/dz² log P)(z₀) = Σ w_i² z₀^{w_i} / (1 + z₀^{w_i})²

  THIS IS O(n) TO COMPUTE. If it distinguishes 0 from ≥1 → polynomial algorithm!
-}

import Data.List (foldl')
import Data.Bits (xor, shiftR, testBit)
import qualified Data.Set as Set
import PeqNP.ActorSolver (padR)

-- | Find saddle point: z₀ such that Σ w_i z^{w_i} / (1+z^{w_i}) = T
-- Uses Newton's method on the positive real axis.
-- Works in LOG SPACE to avoid overflow: track log(z) instead of z.
findSaddlePoint :: [Int] -> Int -> Double
findSaddlePoint weights target =
  let t = fromIntegral target :: Double
      -- Function: g(u) = Σ w_i × exp(w_i × u) / (1 + exp(w_i × u)) - T
      -- where u = log(z), z = exp(u)
      -- g(u) = Σ w_i / (1 + exp(-w_i × u)) - T  (numerically stable form)
      g u = sum [fromIntegral w / (1 + exp (- fromIntegral w * u)) | w <- weights] - t
      -- Derivative: g'(u) = Σ w_i² × exp(-w_i×u) / (1 + exp(-w_i×u))²
      g' u = sum [let e = exp (- fromIntegral w * u)
                      wi = fromIntegral w :: Double
                  in wi * wi * e / (1 + e)^(2::Int)
                 | w <- weights]
      -- Newton iteration
      iterate' u 0 = u
      iterate' u n =
        let gu = g u
            gpu = g' u
            u' = u - gu / gpu
        in iterate' u' (n - 1 :: Int)
      -- Initial guess: u such that n/2 weights are "on" → u ≈ 0
      u0 = 0.0
      uStar = iterate' u0 50
  in exp uStar  -- return z₀ = exp(u*)

-- | Evaluate log P(z₀) = Σ log(1 + z₀^{w_i}) in log space
-- To avoid overflow: log(1 + z^w) = log(1 + exp(w × log z))
-- For large w×log(z): ≈ w × log(z) if z > 1, or ≈ 0 if z < 1 and w large
logPAtSaddle :: [Int] -> Double -> Double
logPAtSaddle weights z0 =
  let logz = log z0
  in sum [log1pexp (fromIntegral w * logz) | w <- weights]
  where
    -- Numerically stable log(1 + exp(x))
    log1pexp x
      | x > 30    = x          -- exp(x) dominates
      | x < -30   = 0          -- exp(x) ≈ 0
      | otherwise  = log (1 + exp x)

-- | Variance at saddle point: V = Σ w_i² z₀^{w_i} / (1 + z₀^{w_i})²
varianceAtSaddle :: [Int] -> Double -> Double
varianceAtSaddle weights z0 =
  let logz = log z0
  in sum [let wl = fromIntegral w * logz
              e = exp (-wl)
              wi = fromIntegral w :: Double
          in wi * wi * e / (1 + e)^(2::Int)
         | w <- weights]

-- | Saddle point approximation: [x^T]P ≈ exp(logP(z₀) - T×log(z₀)) / √(2πV)
saddleApprox :: [Int] -> Int -> (Double, Double, Double, Double)
  -- Returns (approx_coefficient, z0, logP_at_z0, variance)
saddleApprox weights target =
  let z0 = findSaddlePoint weights target
      logPz = logPAtSaddle weights z0
      v = varianceAtSaddle weights z0
      -- log of the approximation (to avoid overflow)
      logApprox = logPz - fromIntegral target * log z0 - 0.5 * log (2 * pi * v)
      approx = exp logApprox
  in (approx, z0, logPz, v)

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
  putStrLn " SADDLE POINT: O(n) coefficient extraction via analysis"
  putStrLn " Can it distinguish [x^T]P = 0 from [x^T]P ≥ 1?"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Test on small instances where we know the answer
  putStrLn "=== SADDLE POINT vs GROUND TRUTH ==="
  putStrLn (padR 5 "n" ++ padR 10 "target" ++ padR 12 "approx"
    ++ padR 8 "DP" ++ padR 10 "detect?" ++ padR 12 "z₀"
    ++ padR 12 "variance")
  putStrLn (replicate 70 '-')

  mapM_ (\n -> do
    let (ws, tNo) = mkHash n
        tYes = sum (take (n `div` 2) ws)
        dpNo = Set.member tNo (dpReachable ws)
        dpYes = Set.member tYes (dpReachable ws)

    -- NO target
    let (approxNo, z0no, _, vNo) = saddleApprox ws tNo
    putStrLn $ padR 5 (show n)
      ++ padR 10 "NO"
      ++ padR 12 (showF 4 approxNo)
      ++ padR 8 (show dpNo)
      ++ padR 10 (if (approxNo < 0.5) == (not dpNo) then "✓" else "✗")
      ++ padR 12 (showF 6 z0no)
      ++ padR 12 (showF 1 vNo)

    -- YES target
    let (approxYes, z0yes, _, vYes) = saddleApprox ws tYes
    putStrLn $ padR 5 (show n)
      ++ padR 10 "YES"
      ++ padR 12 (showF 4 approxYes)
      ++ padR 8 (show dpYes)
      ++ padR 10 (if (approxYes >= 0.5) == dpYes then "✓" else "✗")
      ++ padR 12 (showF 6 z0yes)
      ++ padR 12 (showF 1 vYes)
    putStrLn ""
    ) [6, 8, 10, 12, 14, 16, 18, 20]

  -- Sweep targets around the NO target to see resolution
  putStrLn "=== RESOLUTION TEST: sweep targets near T (n=12) ==="
  let n12 = 12
      (ws12, tNo12) = mkHash n12
      dpSet12 = dpReachable ws12
  putStrLn (padR 10 "target" ++ padR 12 "approx" ++ padR 8 "DP"
    ++ padR 10 "detect?")
  putStrLn (replicate 42 '-')
  mapM_ (\offset -> do
    let t = tNo12 + offset
        (approx, _, _, _) = saddleApprox ws12 t
        dp = Set.member t dpSet12
        detected = if dp then approx >= 0.5 else approx < 0.5
    putStrLn $ padR 10 (show offset)
      ++ padR 12 (showF 4 approx)
      ++ padR 8 (if dp then "YES" else "NO")
      ++ padR 10 (if detected then "✓" else "✗ WRONG")
    ) [-5..5]
  putStrLn ""

  -- Scale test: does precision degrade with n?
  putStrLn "=== SCALING: saddle point quality vs n ==="
  putStrLn (padR 5 "n" ++ padR 14 "approx(NO)" ++ padR 14 "approx(YES)"
    ++ padR 12 "gap" ++ padR 10 "separable?")
  putStrLn (replicate 56 '-')
  mapM_ (\n -> do
    let (ws, tNo) = mkHash n
        tYes = sum (take (n `div` 2) ws)
        (aN, _, _, _) = saddleApprox ws tNo
        (aY, _, _, _) = saddleApprox ws tYes
        gap = aY - aN
    putStrLn $ padR 5 (show n)
      ++ padR 14 (showF 6 aN)
      ++ padR 14 (showF 6 aY)
      ++ padR 12 (showF 6 gap)
      ++ padR 10 (if gap > 0.5 then "YES" else if gap > 0.01 then "maybe" else "NO")
    ) [6, 8, 10, 12, 14, 16, 18, 20, 24, 28, 30]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn "If gap stays > 0.5 as n grows → POLYNOMIAL DETECTOR"
  putStrLn "If gap → 0 → saddle point lacks resolution"
  putStrLn "═══════════════════════════════════════════════════════════"

showF :: Int -> Double -> String
showF decimals x
  | isNaN x = "NaN"
  | isInfinite x = if x > 0 then "+Inf" else "-Inf"
  | otherwise =
      let factor = 10.0 ^^ decimals :: Double
          rounded = fromIntegral (round (x * factor) :: Integer) / factor
      in show rounded
