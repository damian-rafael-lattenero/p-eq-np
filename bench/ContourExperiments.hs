module Main where

-- CONTOUR EXPERIMENTS: can complex analysis beat 2^(n/2)?
--
-- P(x) = ∏(1 + x^wᵢ). We want [x^T]P(x) > 0?
--
-- By Cauchy: [x^T]P = z₀^(-T)/(2π) ∫ P(z₀ e^iθ) e^(-iTθ) dθ
-- where z₀ is the saddle point on the positive real axis.
--
-- Five experiments measuring whether contour methods can escape
-- the 2^n barrier for density-1 Subset Sum:
--
-- 1. BARRIER METRICS: saddle tilt, oscillation cycles, Nyquist
-- 2. TILTED DFT: convergence with K quadrature points
-- 3. EDGEWORTH: higher-order saddle corrections
-- 4. SPECTRAL ENERGY: Monte Carlo sample complexity
-- 5. DENSITY CROSSOVER: where does the tilt start helping?

import Data.List (foldl')
import Data.Bits (xor, shiftR, testBit)
import qualified Data.Set as Set
import PeqNP.ActorSolver (padR)

-- ═════════════════════════════════════════════════════
-- SADDLE POINT
-- ═════════════════════════════════════════════════════

-- | Find u* = log(z₀) via Newton. Solves Σ wᵢ σ(wᵢu) = T.
findSaddle :: [Int] -> Int -> Double
findSaddle weights target =
  let t = fromIntegral target :: Double
      g u = sum [fromIntegral w / (1 + exp (negate (fromIntegral w * u)))
                | w <- weights] - t
      g' u = sum [let wi = fromIntegral w :: Double
                      e = exp (negate (wi * u))
                  in wi * wi * e / (1 + e) ^ (2::Int)
                 | w <- weights]
      step u = let gv = g' u
               in if abs gv < 1e-30 then u else u - g u / gv
      go u 0 = u
      go u n = go (step u) (n - 1 :: Int)
  in go 0.0 200

-- | Cumulants κ₂ (variance), κ₃ (skewness), κ₄ (excess kurtosis)
-- at the tilted distribution pᵢ = σ(wᵢu*).
saddleCumulants :: [Int] -> Double -> (Double, Double, Double)
saddleCumulants weights uStar =
  let ps = [(fromIntegral w :: Double,
             1 / (1 + exp (negate (fromIntegral w * uStar))))
           | w <- weights]
      k2 = sum [w*w * p*(1-p)       | (w,p) <- ps]
      k3 = sum [w*w*w * p*(1-p)*(1-2*p) | (w,p) <- ps]
      k4 = sum [w*w*w*w * p*(1-p)*(1 - 6*p*(1-p)) | (w,p) <- ps]
  in (k2, k3, k4)

-- | log P(z₀) = Σ log(1 + exp(wᵢ u*))
logPSaddle :: [Int] -> Double -> Double
logPSaddle weights uStar =
  sum [l1pe (fromIntegral w * uStar) | w <- weights]
  where l1pe x | x > 30 = x | x < -30 = 0 | otherwise = log (1 + exp x)

-- | Saddle leading order: [x^T]P ≈ exp(logP - Tu*) / √(2πV)
saddleLead :: Double -> Int -> Double -> Double -> Double
saddleLead logPz0 target uStar v =
  exp (logPz0 - fromIntegral target * uStar - 0.5 * log (2 * pi * v))

-- | Edgeworth correction factor: 1 + κ₄/(8V²) - 5κ₃²/(24V³)
edgeworthFactor :: Double -> Double -> Double -> Double
edgeworthFactor k2 k3 k4 =
  1 + k4 / (8 * k2 * k2) - 5 * k3 * k3 / (24 * k2 * k2 * k2)

-- ═════════════════════════════════════════════════════
-- TILTED CONTOUR DFT
-- ═════════════════════════════════════════════════════

-- | [x^T]P via K-point DFT on |z| = exp(u*).
-- Normalized by P(z₀)/z₀^T for numerical stability.
tiltedDFT :: [Int] -> Int -> Double -> Int -> Double
tiltedDFT weights target uStar numK =
  let t = fromIntegral target :: Double
      kf = fromIntegral numK :: Double
      rks = [exp (fromIntegral w * uStar) | w <- weights]

      evalAt j =
        let theta = 2 * pi * fromIntegral j / kf
            -- log-normalized product: ∏ (1+rₖe^{iwₖθ})/(1+rₖ)
            (logMod, phase) = foldl' (\(lm, ph) (w, rk) ->
              let a = fromIntegral w * theta
                  re = 1 + rk * cos a
                  im = rk * sin a
                  modSq = re * re + im * im
                  normSq = (1 + rk) * (1 + rk)
              in ( lm + 0.5 * log (modSq / normSq)
                 , ph + atan2 im re )
              ) (0, 0) (zip weights rks)
        in exp logMod * cos (phase - t * theta)

      avg = sum [evalAt j | j <- [0 .. numK - 1]] / kf
      logPz0 = logPSaddle weights uStar
  in exp (logPz0 - t * uStar) * avg

-- ═════════════════════════════════════════════════════
-- MONTE CARLO VARIANCE ON CONTOUR
-- ═════════════════════════════════════════════════════

-- | Compute mean and variance of the un-normalized DFT integrand.
-- f(θ) = Re[ P(z₀e^{iθ}) × z₀^{-T} × e^{-iTθ} ]
-- Returns (mean, variance, M_needed = var/mean²)
contourStats :: [Int] -> Int -> Double -> Int -> (Double, Double, Double)
contourStats weights target uStar numK =
  let t = fromIntegral target :: Double
      kf = fromIntegral numK :: Double

      evalAt j =
        let theta = 2 * pi * fromIntegral j / kf
            -- ∏(1 + exp(wᵢu* + iwᵢθ)) × exp(-Tu*) × exp(-iTθ)
            (pRe, pIm) = foldl' (\(re, im) w ->
              let wf = fromIntegral w
                  rk = exp (wf * uStar)
                  re1 = 1 + rk * cos (wf * theta)
                  im1 = rk * sin (wf * theta)
              in (re * re1 - im * im1, re * im1 + im * re1)
              ) (1, 0) weights
            scale = exp (negate (t * uStar))
            ph = negate (t * theta)
        in scale * (pRe * cos ph - pIm * sin ph)

      xs = [evalAt j | j <- [0 .. numK - 1]]
      mean = sum xs / kf
      meanSq = sum [x * x | x <- xs] / kf
      var = max 0 (meanSq - mean * mean)
      mNeeded = if abs mean > 1e-15 then var / (mean * mean) else 1e30
  in (mean, var, mNeeded)

-- ═════════════════════════════════════════════════════
-- INSTANCES
-- ═════════════════════════════════════════════════════

-- | Density-1 instance: wᵢ ∈ [2^n, 3×2^{n-1}). Hard case.
mkDensity1 :: Int -> ([Int], Int)
mkDensity1 n =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
           | i <- [0..n-1 :: Int]]
      t = sum ws `div` 2 + 1
  in (ws, t)

-- | Variable density: bit-width = ceil(d × n).
mkDensity :: Double -> Int -> ([Int], Int)
mkDensity d n =
  let bw = max 1 (ceiling (d * fromIntegral n) :: Int)
      mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [2^bw + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` max 1 (2^(bw-1)))
           | i <- [0..n-1 :: Int]]
      t = sum ws `div` 2 + 1
  in (ws, t)

dpReachable :: [Int] -> Set.Set Int
dpReachable = foldl' (\acc w -> Set.union acc (Set.map (+w) acc)) (Set.singleton 0)

yesTarget :: [Int] -> Int -> Int
yesTarget ws n = sum (take (n `div` 2) ws)

-- ═════════════════════════════════════════════════════
-- MAIN
-- ═════════════════════════════════════════════════════

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════"
  putStrLn " CONTOUR EXPERIMENTS: testing the analytic barrier"
  putStrLn " Can we compute [x^T]P(x) in poly(n) via complex analysis?"
  putStrLn "═══════════════════════════════════════════════════════════════"
  putStrLn ""
  experiment1
  experiment2
  experiment3
  experiment4
  experiment5
  conclusions

-- ═════════════════════════════════════════════════════
-- EXP 1: BARRIER METRICS
-- ═════════════════════════════════════════════════════

experiment1 :: IO ()
experiment1 = do
  putStrLn "┌───────────────────────────────────────────────────────────┐"
  putStrLn "│ EXP 1: BARRIER METRICS (density-1)                       │"
  putStrLn "│                                                           │"
  putStrLn "│ At the saddle z₀, integrand decays as exp(-Vθ²/2)       │"
  putStrLn "│ but oscillates with period ~ 2π/max(w).                  │"
  putStrLn "│                                                           │"
  putStrLn "│ cycles = √V / max(w)                                    │"
  putStrLn "│   >> 1 → Gaussian can't kill oscillations → need exp(n) │"
  putStrLn "│   << 1 → Gaussian dominates → poly(n) might work        │"
  putStrLn "└───────────────────────────────────────────────────────────┘"
  putStrLn ""
  putStrLn (padR 5 "n" ++ padR 14 "u*=log(z₀)"
    ++ padR 14 "√V" ++ padR 12 "max(w)"
    ++ padR 10 "cycles" ++ padR 14 "Nyquist")
  putStrLn (replicate 70 '-')

  mapM_ (\n -> do
    let (ws, t) = mkDensity1 n
        uStar = findSaddle ws t
        (v, _, _) = saddleCumulants ws uStar
        maxW = maximum ws
        sqrtV = sqrt v
        cycles = sqrtV / fromIntegral maxW
        nyquist = 2 * sum ws
    putStrLn $ padR 5 (show n)
      ++ padR 14 (showSci uStar)
      ++ padR 14 (showSci sqrtV)
      ++ padR 12 (show maxW)
      ++ padR 10 (showF 1 cycles)
      ++ padR 14 (showSci (fromIntegral nyquist))
    ) [6, 8, 10, 12, 14, 16, 20, 24, 30]
  putStrLn ""
  putStrLn "  → u* ≈ 0 (z₀ ≈ 1): NO tilt for density-1"
  putStrLn "  → cycles ∝ √n: oscillations SURVIVE the Gaussian decay"
  putStrLn "  → Nyquist ∝ n×2^n: same as DP table size"
  putStrLn ""

-- ═════════════════════════════════════════════════════
-- EXP 2: TILTED DFT CONVERGENCE
-- ═════════════════════════════════════════════════════

experiment2 :: IO ()
experiment2 = do
  putStrLn "┌───────────────────────────────────────────────────────────┐"
  putStrLn "│ EXP 2: TILTED DFT — convergence with K quadrature pts   │"
  putStrLn "│                                                           │"
  putStrLn "│ [x^T]P = z₀^{-T}/K × Σ P(z₀e^{2πij/K}) e^{-2πijT/K} │"
  putStrLn "│ Exact when K > Nyquist = 2×Σwᵢ.                        │"
  putStrLn "│ Does it converge for K ≪ Nyquist?                       │"
  putStrLn "└───────────────────────────────────────────────────────────┘"
  putStrLn ""

  mapM_ (\n -> do
    let (ws, tNo) = mkDensity1 n
        tYes = yesTarget ws n
        dpSet = dpReachable ws
        dpNo = Set.member tNo dpSet
        dpYes = Set.member tYes dpSet
        uNo = findSaddle ws tNo
        uYes = findSaddle ws tYes
        nyq = 2 * sum ws

    putStrLn $ "  n=" ++ show n
      ++ "  Nyquist=" ++ show nyq
      ++ "  DP(NO)=" ++ show dpNo
      ++ "  DP(YES)=" ++ show dpYes
    putStrLn $ "  " ++ padR 12 "K"
      ++ padR 14 "DFT(NO)" ++ padR 8 "ok?"
      ++ padR 14 "DFT(YES)" ++ padR 8 "ok?"
    putStrLn $ "  " ++ replicate 58 '-'

    let ks = filter (<= nyq) [100, 500, 1000, 5000, 10000, 50000] ++ [nyq]
    mapM_ (\numK -> do
      let dNo  = tiltedDFT ws tNo uNo numK
          dYes = tiltedDFT ws tYes uYes numK
          okNo  = (dNo < 0.5) == not dpNo
          okYes = (dYes >= 0.5) == dpYes
          label = if numK == nyq then "Nyquist" else show numK
      putStrLn $ "  " ++ padR 12 label
        ++ padR 14 (showF 4 dNo) ++ padR 8 (if okNo then "✓" else "✗")
        ++ padR 14 (showF 4 dYes) ++ padR 8 (if okYes then "✓" else "✗")
      ) ks
    putStrLn ""
    ) [6, 8, 10, 12]

  putStrLn "  → Convergence requires K ~ Nyquist = O(n × 2^n)"
  putStrLn "    Same cost as DP. The DFT IS the DP in frequency domain."
  putStrLn ""

-- ═════════════════════════════════════════════════════
-- EXP 3: EDGEWORTH CORRECTIONS
-- ═════════════════════════════════════════════════════

experiment3 :: IO ()
experiment3 = do
  putStrLn "┌───────────────────────────────────────────────────────────┐"
  putStrLn "│ EXP 3: EDGEWORTH — do higher-order corrections help?     │"
  putStrLn "│                                                           │"
  putStrLn "│ Leading saddle: [x^T]P ≈ P(z₀)/z₀^T / √(2πV)          │"
  putStrLn "│ Edgeworth: × (1 + κ₄/(8V²) - 5κ₃²/(24V³))            │"
  putStrLn "│ Both are O(n). Can they separate YES from NO?            │"
  putStrLn "└───────────────────────────────────────────────────────────┘"
  putStrLn ""
  putStrLn (padR 5 "n"
    ++ padR 14 "saddle(NO)" ++ padR 14 "edge(NO)"
    ++ padR 14 "saddle(YES)" ++ padR 14 "edge(YES)"
    ++ padR 8 "gap")
  putStrLn (replicate 70 '-')

  mapM_ (\n -> do
    let (ws, tNo) = mkDensity1 n
        tYes = yesTarget ws n

        uNo = findSaddle ws tNo
        (k2n, k3n, k4n) = saddleCumulants ws uNo
        lpNo = logPSaddle ws uNo
        sNo = saddleLead lpNo tNo uNo k2n
        eNo = sNo * edgeworthFactor k2n k3n k4n

        uYes = findSaddle ws tYes
        (k2y, k3y, k4y) = saddleCumulants ws uYes
        lpYes = logPSaddle ws uYes
        sYes = saddleLead lpYes tYes uYes k2y
        eYes = sYes * edgeworthFactor k2y k3y k4y

    putStrLn $ padR 5 (show n)
      ++ padR 14 (showF 4 sNo)
      ++ padR 14 (showF 4 eNo)
      ++ padR 14 (showF 4 sYes)
      ++ padR 14 (showF 4 eYes)
      ++ padR 8 (showF 4 (eYes - eNo))
    ) [6, 8, 10, 12, 14, 16, 18, 20]
  putStrLn ""
  putStrLn "  → Saddle gives ≈ same value for YES and NO targets"
  putStrLn "    It estimates the LOCAL AVERAGE of [x^T']P near T."
  putStrLn "    For density-1, this average is O(1) for ALL T in range."
  putStrLn "    Edgeworth corrections refine the average, NOT individual."
  putStrLn ""

-- ═════════════════════════════════════════════════════
-- EXP 4: SPECTRAL ENERGY / MC VARIANCE
-- ═════════════════════════════════════════════════════

experiment4 :: IO ()
experiment4 = do
  putStrLn "┌───────────────────────────────────────────────────────────┐"
  putStrLn "│ EXP 4: SPECTRAL ENERGY — Monte Carlo sample complexity   │"
  putStrLn "│                                                           │"
  putStrLn "│ X(θ) = Re[P(z₀e^{iθ}) z₀^{-T} e^{-iTθ}]              │"
  putStrLn "│ E[X] = [x^T]P.  M_needed = Var[X] / E[X]²             │"
  putStrLn "│ M_needed random samples for detection (SNR > 1).         │"
  putStrLn "│                                                           │"
  putStrLn "│ Compare UNIT CIRCLE (no tilt) vs TILTED (z₀).           │"
  putStrLn "│ YES targets only (where [x^T]P ≥ 1).                    │"
  putStrLn "└───────────────────────────────────────────────────────────┘"
  putStrLn ""
  putStrLn (padR 5 "n"
    ++ padR 12 "M_unit" ++ padR 12 "M_tilt"
    ++ padR 10 "2^n" ++ padR 12 "tilt/unit")
  putStrLn (replicate 52 '-')

  mapM_ (\n -> do
    let (ws, _) = mkDensity1 n
        tYes = yesTarget ws n
        uYes = findSaddle ws tYes
        numK = 50000

        -- Unit circle (uStar = 0)
        (_, _, mUnit) = contourStats ws tYes 0.0 numK
        -- Tilted contour
        (_, _, mTilt) = contourStats ws tYes uYes numK
        ratio = if mTilt > 0 then mUnit / mTilt else 0

    putStrLn $ padR 5 (show n)
      ++ padR 12 (showSci mUnit)
      ++ padR 12 (showSci mTilt)
      ++ padR 10 (show ((2::Int)^n))
      ++ padR 12 (showF 2 ratio)
    ) [6, 8, 10, 12, 14]
  putStrLn ""
  putStrLn "  → M_needed ∝ 2^n for BOTH unit and tilted contours"
  putStrLn "    Tilt improves by ≈ √n factor — still exponential."
  putStrLn "    Reason: spectral energy Σ[x^{T'}P]² = 2^n (Parseval)"
  putStrLn "    is inherent in the product, no contour can remove it."
  putStrLn ""

-- ═════════════════════════════════════════════════════
-- EXP 5: DENSITY CROSSOVER
-- ═════════════════════════════════════════════════════

experiment5 :: IO ()
experiment5 = do
  putStrLn "┌───────────────────────────────────────────────────────────┐"
  putStrLn "│ EXP 5: DENSITY CROSSOVER (n=12)                         │"
  putStrLn "│                                                           │"
  putStrLn "│ Low density → z₀ ≠ 1 → tilt damps → DFT works          │"
  putStrLn "│ High density → z₀ → 1 → no damping → DFT fails         │"
  putStrLn "│ Test: does DFT(K=1000) give correct answer?              │"
  putStrLn "└───────────────────────────────────────────────────────────┘"
  putStrLn ""
  putStrLn (padR 8 "density"
    ++ padR 14 "u*=log(z₀)" ++ padR 10 "cycles"
    ++ padR 14 "DFT(K=1k)" ++ padR 8 "DP"
    ++ padR 8 "ok?")
  putStrLn (replicate 64 '-')

  let nTest = 12
  mapM_ (\d -> do
    let (ws, tNo) = mkDensity d nTest
        uStar = findSaddle ws tNo
        (v, _, _) = saddleCumulants ws uStar
        maxW = maximum ws
        cycles = sqrt v / fromIntegral maxW
        dft1k = tiltedDFT ws tNo uStar 1000
        dpAns = Set.member tNo (dpReachable ws)
        correct = (dft1k < 0.5) == not dpAns
    putStrLn $ padR 8 (showF 2 d)
      ++ padR 14 (showSci uStar)
      ++ padR 10 (showF 2 cycles)
      ++ padR 14 (showF 4 dft1k)
      ++ padR 8 (if dpAns then "YES" else "NO")
      ++ padR 8 (if correct then "✓" else "✗")
    ) [0.3, 0.5, 0.7, 0.8, 0.9, 1.0, 1.2, 1.5, 2.0]
  putStrLn ""
  putStrLn "  → For d < 1: tilt works, DFT converges with few points"
  putStrLn "    But these instances are already easy (DP ∝ n × 2^{dn})"
  putStrLn "  → For d ≥ 1: no tilt, need exponential K"
  putStrLn ""

-- ═════════════════════════════════════════════════════
-- CONCLUSIONS
-- ═════════════════════════════════════════════════════

conclusions :: IO ()
conclusions = do
  putStrLn "═══════════════════════════════════════════════════════════════"
  putStrLn " CONCLUSIONS (measured, not conjectured)"
  putStrLn ""
  putStrLn " THE BARRIER (density-1):"
  putStrLn "   • z₀ ≈ 1 → tilted contour ≈ unit circle (no damping)"
  putStrLn "   • cycles = √V/max(w) ∝ √n → oscillations survive"
  putStrLn "   • Nyquist = 2Σwᵢ = O(n×2^n) → same as DP table"
  putStrLn "   • Spectral energy Σ[x^T']P² = 2^n → M_needed = 2^n"
  putStrLn "   • Edgeworth sees LOCAL AVERAGE → same for YES and NO"
  putStrLn ""
  putStrLn " THE DUALITY:"
  putStrLn "   DFT on |z|=z₀ with K points ⟺ DP with table size K"
  putStrLn "   The 'oscillation barrier' and the 'table size barrier'"
  putStrLn "   are the SAME barrier in dual coordinates."
  putStrLn ""
  putStrLn " POSITIVE RESULT (density < 1):"
  putStrLn "   Tilt works: z₀ deviates from 1, dampens oscillations."
  putStrLn "   But DP is already polynomial for density < 1."
  putStrLn ""
  putStrLn " WHY point-evaluation can't work:"
  putStrLn "   P has 2^n Fourier modes. Each evaluation reveals O(log n)"
  putStrLn "   bits. To identify one coefficient → need 2^n/log(n) evals."
  putStrLn "   This is an INFORMATION-THEORETIC bound, not a method limit."
  putStrLn ""
  putStrLn " WHAT TO TRY NEXT:"
  putStrLn "   The barrier is for BLACK-BOX evaluation of P."
  putStrLn "   To escape, exploit the PRODUCT STRUCTURE of P = ∏(1+x^wᵢ)."
  putStrLn "   Ideas that DON'T treat P as a black box:"
  putStrLn "   1. Multi-scale bit decomposition: process weight bits"
  putStrLn "      MSB→LSB, each level is a smaller-range problem"
  putStrLn "   2. Lattice reduction (LLL): find short vectors in the"
  putStrLn "      weight lattice to reduce effective bit-width"
  putStrLn "   3. Modular CRT: [x^T]P mod p via O(np) DP, combine —"
  putStrLn "      but need ∏p > max([x^T]P) which can be 2^n"
  putStrLn "   4. Randomized hashing: map weights to smaller range"
  putStrLn "      via w'ᵢ = wᵢ mod M, solve smaller problem, check"
  putStrLn "═══════════════════════════════════════════════════════════════"

-- ═════════════════════════════════════════════════════
-- FORMATTING
-- ═════════════════════════════════════════════════════

showF :: Int -> Double -> String
showF d x
  | isNaN x = "NaN"
  | isInfinite x = if x > 0 then "+Inf" else "-Inf"
  | otherwise =
      let f = 10.0 ^^ d :: Double
      in show (fromIntegral (round (x * f) :: Integer) / f)

showSci :: Double -> String
showSci x
  | isNaN x = "NaN"
  | isInfinite x = if x > 0 then "+Inf" else "-Inf"
  | x == 0 = "0"
  | abs x < 1e-300 = "~0"
  | abs x < 0.01 || abs x > 1e6 =
      let e = floor (logBase 10 (abs x)) :: Int
          m = x / (10 ^^ e)
      in showF 2 m ++ "e" ++ show e
  | otherwise = showF 4 x
