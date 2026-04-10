module Main where


import Data.List (foldl')
import Data.Bits (xor, shiftR, testBit)
import qualified Data.Set as Set
import PeqNP.ActorSolver (padR)

-- | Exact flare: Σ_{S⊆[n]} e^{-β(sum(S)-T)²}
-- Brute force: O(2^n). For ground truth only.
exactFlare :: [Int] -> Int -> Double -> Double
exactFlare weights target beta =
  let n = length weights
  in sum [ exp (-beta * fromIntegral ((s - target)^(2::Int)))
         | mask <- [0..(2::Int)^n - 1]
         , let s = subsetSum mask weights
         ]
  where
    subsetSum mask ws = sum [w | (i,w) <- zip [0..] ws, testBit mask i]

-- | Hubbard-Stratonovich flare: numerical integration
-- Flare = √(1/(4πβ)) × ∫ e^{-u²/(4β)} × e^{-iuT} × P(e^{iu}) du
-- Discretize: u = k×Δu for k = -K..K, Δu = π/W where W > max possible sum
hsFlare :: [Int] -> Int -> Double -> Int -> Double
hsFlare weights target beta numPoints =
  let maxSum = sum weights
      -- Integration range: u ∈ [-uMax, uMax] where Gaussian is significant
      -- e^{-u²/(4β)} is significant for |u| < √(4β × cutoff)
      uMax = sqrt (4 * beta * 20)  -- cutoff at e^{-20} ≈ 2e-9
      du = 2 * uMax / fromIntegral numPoints
      t = fromIntegral target :: Double

      -- Evaluate integrand at each quadrature point
      integrand u =
        let -- e^{-u²/(4β)}
            gaussPart = exp (-u*u / (4 * beta))
            -- e^{-iuT} × P(e^{iu}) — need real part
            -- P(e^{iu}) = ∏(1 + e^{iuw_k})
            -- Accumulate as (re, im)
            (pRe, pIm) = foldl' (\(re, im) w ->
              let angle = u * fromIntegral w
                  re1 = 1 + cos angle
                  im1 = sin angle
              in (re * re1 - im * im1, re * im1 + im * re1)
              ) (1, 0) weights
            -- Multiply by e^{-iuT}
            phaseRe = cos (-u * t)
            phaseIm = sin (-u * t)
            resultRe = pRe * phaseRe - pIm * phaseIm
        in gaussPart * resultRe

      -- Trapezoidal integration
      total = du * sum [integrand (fromIntegral k * du - uMax)
                       | k <- [0..numPoints]]
      -- Normalization: √(1/(4πβ))
      norm = sqrt (1 / (4 * pi * beta))
  in norm * total

-- | Incremental Gaussian DP: track Flare through construction
-- Instead of tracking [x^T]P, track the smoothed version.
-- F_0 = e^{-β(0-T)²}  (only empty subset, sum=0)
-- F_i = F_{i-1} + contribution from adding w_i
--
-- Actually: F_i = Σ_{S⊆{1..i}} e^{-β(sum(S)-T)²}
-- F_i = F_{i-1} + Σ_{S⊆{1..i}, i∈S} e^{-β(sum(S)-T)²}
--      = F_{i-1} + Σ_{S'⊆{1..i-1}} e^{-β(sum(S')+w_i-T)²}
--
-- So we need: Σ_{S'⊆{1..i-1}} e^{-β(sum(S')+w_i-T)²}
-- = Σ_{S'} e^{-β((sum(S')-T) + w_i)²}
-- = Σ_{S'} e^{-β(sum(S')-T)²} × e^{-β(2w_i(sum(S')-T) + w_i²)}
--
-- The cross term 2w_i(sum(S')-T) couples everything. Can't factor.
-- UNLESS β is very small (linearize the exponential).
--
-- For small β: e^{-β(s+w-T)²} ≈ e^{-β(s-T)²} × e^{-β(2w(s-T)+w²)}
--                              ≈ e^{-β(s-T)²} × (1 - β(2w(s-T)+w²))
-- The correction depends on s — still coupled.

-- | Instead: use the Hubbard-Stratonovich integral with varying number of
-- quadrature points. Measure how many points are needed to get the right answer.
main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " GAUSSIAN FLARE: the bengala as smoothed detection"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  let n = 12
      (ws, tNo) = mkHash n
      tYes = sum (take (n `div` 2) ws)
      dpSet = dpReachable ws

  putStrLn $ "n=" ++ show n ++ ", 2^n=" ++ show ((2::Int)^n)
  putStrLn ""

  -- Part 1: Exact flare for different β values
  putStrLn "=== EXACT FLARE: how β affects resolution ==="
  putStrLn (padR 12 "β" ++ padR 14 "Flare(NO)" ++ padR 14 "Flare(YES)"
    ++ padR 14 "ratio" ++ padR 10 "σ")
  putStrLn (replicate 66 '-')
  mapM_ (\beta -> do
    let fNo  = exactFlare ws tNo beta
        fYes = exactFlare ws tYes beta
        ratio = if fNo > 0 then fYes / fNo else 0
        sigma = sqrt (1 / (2 * beta))
    putStrLn $ padR 12 (showSci beta)
      ++ padR 14 (showSci fNo)
      ++ padR 14 (showSci fYes)
      ++ padR 14 (showF 3 ratio)
      ++ padR 10 (showF 1 sigma)
    ) [1e-10, 1e-8, 1e-6, 1e-4, 1e-3, 1e-2, 0.1, 1.0]
  putStrLn ""

  -- Part 2: HS integral — how many quadrature points needed?
  putStrLn "=== HUBBARD-STRATONOVICH: quadrature convergence ==="
  let beta = 1e-4  -- moderate smoothing
  putStrLn $ "  β = " ++ show beta ++ ", σ = " ++ showF 1 (sqrt (1/(2*beta)))
  putStrLn ""
  putStrLn (padR 10 "points" ++ padR 16 "HS(NO)" ++ padR 16 "HS(YES)"
    ++ padR 16 "exact(NO)" ++ padR 16 "exact(YES)")
  putStrLn (replicate 76 '-')
  let eNo  = exactFlare ws tNo beta
      eYes = exactFlare ws tYes beta
  mapM_ (\numPts -> do
    let hsNo  = hsFlare ws tNo beta numPts
        hsYes = hsFlare ws tYes beta numPts
    putStrLn $ padR 10 (show numPts)
      ++ padR 16 (showSci hsNo)
      ++ padR 16 (showSci hsYes)
      ++ padR 16 (showSci eNo)
      ++ padR 16 (showSci eYes)
    ) [10, 50, 100, 500, 1000, 5000]
  putStrLn ""

  -- Part 3: The money question — for what β can we separate YES from NO?
  putStrLn "=== THE MONEY QUESTION: separability vs β ==="
  putStrLn "  For each β: can Flare(YES) / Flare(NO) > threshold?"
  putStrLn ""
  putStrLn (padR 12 "β" ++ padR 10 "σ" ++ padR 14 "F(NO)" ++ padR 14 "F(YES)"
    ++ padR 14 "F(YES)/F(NO)" ++ padR 10 "sep?")
  putStrLn (replicate 76 '-')
  mapM_ (\beta' -> do
    let fNo' = exactFlare ws tNo beta'
        fYes' = exactFlare ws tYes beta'
        ratio' = if fNo' > 1e-300 then fYes' / fNo' else 0
        sigma' = sqrt (1 / (2 * beta'))
    putStrLn $ padR 12 (showSci beta')
      ++ padR 10 (showF 0 sigma')
      ++ padR 14 (showSci fNo')
      ++ padR 14 (showSci fYes')
      ++ padR 14 (showF 6 ratio')
      ++ padR 10 (if abs (ratio' - 1) > 0.1 then "YES" else "no")
    ) [1e-12, 1e-10, 1e-8, 1e-6, 1e-5, 1e-4, 1e-3, 1e-2, 0.1, 1.0, 10.0]
  putStrLn ""

  -- Part 4: THE SCALING TEST
  putStrLn "=== SCALING: does the flare ratio survive as n grows? ==="
  putStrLn "  HS with 500 points, beta=1/n^2 (sigma~n)"
  putStrLn ""
  putStrLn (padR 5 "n" ++ padR 14 "HS(NO)" ++ padR 14 "HS(YES)"
    ++ padR 12 "ratio" ++ padR 10 "signal?")
  putStrLn (replicate 58 '-')
  mapM_ (\ni -> do
    let (wsi, tNoi) = mkHash ni
        tYesi = sum (take (ni `div` 2) wsi)
        betai = 1.0 / (fromIntegral ni * fromIntegral ni) :: Double
        numPts = 500
        hsNo'  = hsFlare wsi tNoi betai numPts
        hsYes' = hsFlare wsi tYesi betai numPts
        r = if abs hsNo' > 1e-10 then hsYes' / hsNo' else 0
    putStrLn $ padR 5 (show ni)
      ++ padR 14 (showSci hsNo')
      ++ padR 14 (showSci hsYes')
      ++ padR 12 (showF 4 r)
      ++ padR 10 (if abs (r - 1) > 0.05 then "YES" else "no")
    ) [8, 10, 12, 14, 16, 18, 20, 24, 28, 32, 40, 50, 60]
  putStrLn ""

  -- Part 5: Fixed beta=0.01, exact flare, small n
  putStrLn "=== FIXED beta=0.01: exact ratio vs n ==="
  putStrLn (padR 5 "n" ++ padR 14 "exact(NO)" ++ padR 14 "exact(YES)"
    ++ padR 12 "ratio" ++ padR 10 "signal?")
  putStrLn (replicate 58 '-')
  mapM_ (\ni -> do
    let (wsi, tNoi) = mkHash ni
        tYesi = sum (take (ni `div` 2) wsi)
        betaF = 0.01 :: Double
        fNo'  = exactFlare wsi tNoi betaF
        fYes' = exactFlare wsi tYesi betaF
        r = if fNo' > 1e-300 then fYes' / fNo' else 0
    putStrLn $ padR 5 (show ni)
      ++ padR 14 (showSci fNo')
      ++ padR 14 (showSci fYes')
      ++ padR 12 (showF 4 r)
      ++ padR 10 (if abs (r - 1) > 0.05 then "YES" else "no")
    ) [6, 8, 10, 12, 14, 16]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn "If ratio stays away from 1.0 → POLYNOMIAL DETECTOR"
  putStrLn "If ratio converges to 1.0 → flare loses power"
  putStrLn "═══════════════════════════════════════════════════════════"

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

showF :: Int -> Double -> String
showF d x
  | isNaN x = "NaN"
  | isInfinite x = "Inf"
  | otherwise = let f = 10.0 ^^ d :: Double
                in show (fromIntegral (round (x * f) :: Integer) / f)

showSci :: Double -> String
showSci x
  | isNaN x = "NaN"
  | isInfinite x = "Inf"
  | x == 0 = "0"
  | abs x < 1e-300 = "~0"
  | abs x < 0.01 || abs x > 1e6 =
      let e = floor (logBase 10 (abs x)) :: Int
          m = x / (10 ^^ e)
      in showF 2 m ++ "e" ++ show e
  | otherwise = showF 4 x
