module Main where

-- MOEBIUS LIFT: twist the DP into a higher-dimensional surface
--
-- Standard DP lives on a LINE: partial sums s in [0..T].
-- MITM is the Moebius twist: identify s with (T-s) at the midpoint.
--
-- NEW IDEA: lift to a TORUS Z/M x Z/N.
-- Track (s mod M, s mod N) instead of s. By CRT, if gcd(M,N)=1 and MxN > T,
-- this is lossless. But MxN can be ~ T with M,N ~ sqrt(T).
--
-- TWIST: add Moebius identification (s, k) with (T-s, n-k) on the torus.
-- This combines CRT decomposition with MITM complement symmetry.
--
-- Also: lift to COMPLEX PLANE. P(exp(i*theta)) on the unit circle.
-- Coefficient extraction via numerical integration of the contour integral.

import qualified Data.Set as Set
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import Data.List (foldl', sort)
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- ═══════════════════════════════════════════════════════════════
-- SECTION A: TORUS DP — track (s mod M, s mod N)
-- ═══════════════════════════════════════════════════════════════

-- | State on the torus: (residue mod M, residue mod N)
type TorusPoint = (Int, Int)

-- | DP on the torus Z/M × Z/N
-- Returns: (is_target_reachable_on_torus, peak_states, total_states)
torusDP :: [Int] -> Int -> Int -> Int -> (Bool, Int, Int)
torusDP weights target m n_ =
  let tTarget = (target `mod` m, target `mod` n_)
      step :: Set.Set TorusPoint -> Int -> Set.Set TorusPoint
      step states w =
        let wPoint = (w `mod` m, w `mod` n_)
            new = Set.map (\(a, b) -> ((a + fst wPoint) `mod` m, (b + snd wPoint) `mod` n_)) states
        in Set.union states new
      allStates = foldl' step (Set.singleton (0, 0)) weights
      peak = m * n_  -- max possible states on torus
  in (Set.member tTarget allStates, Set.size allStates, peak)

-- | Standard 1D DP for comparison
linearDP :: [Int] -> Int -> (Bool, Int)
linearDP weights target =
  let final = foldl' (\acc w -> IS.union acc (IS.map (+w) (IS.filter (<= target - w) acc))) (IS.singleton 0) weights
  in (IS.member target final, IS.size final)

-- ═══════════════════════════════════════════════════════════════
-- SECTION B: MÖBIUS TWIST — complement identification on torus
-- ═══════════════════════════════════════════════════════════════

-- | Möbius-twisted torus: identify (a,b) with ((T-a) mod M, (T-b) mod N)
-- This means s and T-s map to the same equivalence class
moebiusDP :: [Int] -> Int -> Int -> Int -> (Bool, Int)
moebiusDP weights target m n_ =
  let tTarget = (target `mod` m, target `mod` n_)
      -- Möbius identification: canonical representative of {p, twist(p)}
      twist (a, b) = ((target - a) `mod` m, (target - b) `mod` n_)
      canonical p = min p (twist p)  -- choose lexicographically smaller
      step :: Set.Set TorusPoint -> Int -> Set.Set TorusPoint
      step states w =
        let wPoint = (w `mod` m, w `mod` n_)
            new = Set.map (\(a, b) -> canonical ((a + fst wPoint) `mod` m, (b + snd wPoint) `mod` n_)) states
            old = Set.map canonical states
        in Set.union old new
      initState = Set.singleton (canonical (0, 0))
      -- Process only first half of weights (Möbius handles the rest)
      halfWeights = take (length weights `div` 2) weights
      leftStates = foldl' step initState halfWeights
  in (Set.member (canonical tTarget) leftStates, Set.size leftStates)

-- ═══════════════════════════════════════════════════════════════
-- SECTION C: COMPLEX CIRCLE — P(exp(i*theta)) evaluation
-- ═══════════════════════════════════════════════════════════════

-- | Evaluate |P(exp(i*theta))| = ∏|1 + e^{i·wₖ·θ}| = ∏ 2|cos(wₖθ/2)|
magnitudeAtTheta :: [Int] -> Double -> Double
magnitudeAtTheta weights theta =
  product [2.0 * abs (cos (fromIntegral w * theta / 2.0)) | w <- weights]

-- | The integrand for coefficient extraction:
-- Re[P(exp(i*theta)) · exp(-i*T*theta)] (real part of the integrand)
-- [x^T]P = (1/2π) ∫₀²π P(exp(i*theta)) exp(-i*T*theta) dθ
integrandReal :: [Int] -> Int -> Double -> Double
integrandReal weights target theta =
  let -- P(exp(i*theta)) = ∏(1 + e^{i·wₖ·θ})
      -- = ∏ 2cos(wₖθ/2) · e^{i·wₖθ/2}
      -- magnitude = ∏ 2|cos(wₖθ/2)|
      -- phase = Σ wₖθ/2
      mag = product [2.0 * cos (fromIntegral w * theta / 2.0) | w <- weights]
      phase = sum [fromIntegral w * theta / 2.0 | w <- weights]
      -- Integrand = mag · exp(i*(phase - T*theta))
      totalPhase = phase - fromIntegral target * theta
  in mag * cos totalPhase

-- | Numerical coefficient extraction via trapezoidal rule with q points
numericalCoeff :: [Int] -> Int -> Int -> Double
numericalCoeff weights target q =
  let dtheta = 2.0 * pi / fromIntegral q
      sumVal = sum [integrandReal weights target (fromIntegral j * dtheta) | j <- [0..q-1]]
  in sumVal / fromIntegral q

-- | Detect YES/NO by sampling the integrand at q points
complexDetect :: [Int] -> Int -> Int -> (Double, Bool)
complexDetect weights target q =
  let coeff = numericalCoeff weights target q
  in (coeff, abs coeff > 0.5)

mkHash :: Int -> ([Int], Int)
mkHash n =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
           | i <- [0..n-1 :: Int]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

mkHashYes :: Int -> ([Int], Int)
mkHashYes n = let (ws, _) = mkHash n in (ws, sum (take (n `div` 2) ws))

showF :: Int -> Double -> String
showF d x = let f = 10 ^ d :: Int
                r = fromIntegral (round (x * fromIntegral f) :: Int) / fromIntegral f :: Double
            in show r

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn " MÖBIUS LIFT: twist the problem into higher-dimensional surfaces"
  putStrLn " Torus (CRT), Möbius twist (complement), Complex circle"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Torus DP — states on Z/M × Z/N vs linear
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. TORUS DP: states on Z/M × Z/N ==="
  putStrLn "   (CRT: if M×N > T and gcd(M,N)=1, torus is lossless)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 8 "M" ++ padR 8 "N"
    ++ padR 12 "torus-st" ++ padR 10 "M×N"
    ++ padR 10 "linear" ++ padR 8 "corr"
  putStrLn (replicate 68 '-')
  mapM_ (\n -> do
    let (wsY, tY) = mkHashYes n
        (wsN, tN) = mkHash n
        -- Choose M, N as coprime factors of a number > T
        m = 97; n' = 101  -- coprime primes
    -- YES
    let (torYes, torStY, _) = torusDP wsY tY m n'
        (linYes, linStY) = linearDP wsY tY
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 8 (show m) ++ padR 8 (show n')
      ++ padR 12 (show torStY)
      ++ padR 10 (show (m * n'))
      ++ padR 10 (show linStY)
      ++ padR 8 (if torYes == linYes then "OK" else "DIFF!")
    -- NO
    let (torNo, torStN, _) = torusDP wsN tN m n'
        (linNo, linStN) = linearDP wsN tN
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 8 (show m) ++ padR 8 (show n')
      ++ padR 12 (show torStN)
      ++ padR 10 (show (m * n'))
      ++ padR 10 (show linStN)
      ++ padR 8 (if torNo == linNo then "OK" else "FP!")
    ) [6, 8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Torus saturation — what fraction of M×N is filled?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. TORUS SATURATION: fraction of M×N occupied ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 8 "M×N" ++ padR 12 "occupied" ++ padR 10 "fill%"
    ++ padR 12 "linear-st" ++ padR 10 "compress"
  putStrLn (replicate 58 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        pairs = [(m, n') | m <- [7,13,29,53,97], n' <- [11,17,31,59,101],
                           m /= n', gcd m n' == 1, m * n' > 200]
        -- Pick best: smallest M×N with least saturation
        best = head $ sort [(m*n', m, n') | (m, n') <- pairs, m * n' < t]
        (mn, m, n') = best
        (_, torSt, _) = torusDP ws t m n'
        (_, linSt) = linearDP ws t
        fill = fromIntegral torSt / fromIntegral mn * 100 :: Double
        compress = fromIntegral linSt / fromIntegral (max 1 torSt) :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 8 (show mn)
      ++ padR 12 (show torSt)
      ++ padR 10 (showF 1 fill ++ "%")
      ++ padR 12 (show linSt)
      ++ padR 10 (showF 2 compress ++ "x")
    ) [6, 8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Möbius twist — complement identification
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. MÖBIUS TWIST: torus + complement identification ==="
  putStrLn "   (identify (s mod M, s mod N) with (T-s mod M, T-s mod N))"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 12 "torus-st"
    ++ padR 12 "moebius-st" ++ padR 10 "compress" ++ padR 8 "corr"
  putStrLn (replicate 54 '-')
  mapM_ (\n -> do
    let m = 97; n' = 101
    -- YES
    let (wsY, tY) = mkHashYes n
        (_, torStY, _) = torusDP wsY tY m n'
        (moebYes, moebStY) = moebiusDP wsY tY m n'
        (linYes, _) = linearDP wsY tY
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 12 (show torStY)
      ++ padR 12 (show moebStY)
      ++ padR 10 (showF 2 (fromIntegral torStY / fromIntegral (max 1 moebStY) :: Double) ++ "x")
      ++ padR 8 (if moebYes == linYes then "OK" else "ERR")
    -- NO
    let (wsN, tN) = mkHash n
        (_, torStN, _) = torusDP wsN tN m n'
        (moebNo, moebStN) = moebiusDP wsN tN m n'
        (linNo, _) = linearDP wsN tN
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 12 (show torStN)
      ++ padR 12 (show moebStN)
      ++ padR 10 (showF 2 (fromIntegral torStN / fromIntegral (max 1 moebStN) :: Double) ++ "x")
      ++ padR 8 (if moebNo == linNo then "OK" else "FP!")
    ) [6, 8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: Complex circle — numerical coefficient extraction
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. COMPLEX CIRCLE: [x^T]P via numerical integration ==="
  putStrLn "   [x^T]P = (1/2π) ∫ P(exp(i*theta))exp(-i*T*theta)dθ ≈ (1/q)Σ integrand"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 8 "q" ++ padR 14 "num-coeff"
    ++ padR 10 "exact" ++ padR 10 "detect"
  putStrLn (replicate 54 '-')
  mapM_ (\n -> do
    let (wsY, tY) = mkHashYes n
        (wsN, tN) = mkHash n
        (linYes, _) = linearDP wsY tY
        (linNo, _) = linearDP wsN tN
    mapM_ (\q -> do
      let (coeffY, detectY) = complexDetect wsY tY q
          (coeffN, detectN) = complexDetect wsN tN q
      putStrLn $ padR 5 (show n) ++ padR 6 "YES" ++ padR 8 (show q)
        ++ padR 14 (showF 4 coeffY)
        ++ padR 10 (show linYes)
        ++ padR 10 (if detectY == linYes then "OK" else "MISS")
      putStrLn $ padR 5 (show n) ++ padR 6 "NO" ++ padR 8 (show q)
        ++ padR 14 (showF 4 coeffN)
        ++ padR 10 (show linNo)
        ++ padR 10 (if detectN == (not linNo) then "OK" else if detectN then "FP" else "OK")
      ) [100, 500, 2000]
    ) [6, 8]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: Required q for correct detection
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. COMPLEX DETECTION: min q samples for correct answer ==="
  putStrLn "   (if q = O(poly(n)): complex lift gives poly-time algorithm!)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "target" ++ padR 10 "q=n²"
    ++ padR 10 "q=n³" ++ padR 10 "q=T/n" ++ padR 10 "q=T"
  putStrLn (replicate 56 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
        detect q = let (_, d) = complexDetect ws t q in d
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show t)
      ++ padR 10 (show (detect (n*n)))
      ++ padR 10 (show (detect (n*n*n)))
      ++ padR 10 (show (detect (t `div` max 1 n)))
      ++ padR 10 (show (detect t))
    ) [6, 8, 10]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "ANALYSIS:"
  putStrLn " TORUS: the 2D surface compresses linear states by mapping to"
  putStrLn " (s mod M, s mod N). But for density-1, the torus SATURATES"
  putStrLn " (all M×N points occupied) — same as modular markers."
  putStrLn ""
  putStrLn " MÖBIUS TWIST: complement identification on the torus gives ~2x"
  putStrLn " compression (same as MITM). The twist IS MITM in disguise."
  putStrLn ""
  putStrLn " COMPLEX CIRCLE: P(exp(i*theta)) oscillates rapidly for large T."
  putStrLn " With q samples: aliasing prevents detection for q << T."
  putStrLn " Need q ≈ T for correct answer — O(nT) total, same as DP."
  putStrLn ""
  putStrLn " The Möbius strip insight was correct: MITM IS the twist."
  putStrLn " Going further requires a HIGHER-ORDER twist — not just"
  putStrLn " one identification, but a cascade of identifications."
  putStrLn " That's exactly what the multi-level sieve does (O(2^{0.32n}))."
  putStrLn "═══════════════════════════════════════════════════════════════════"
