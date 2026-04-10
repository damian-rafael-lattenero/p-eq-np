module Main where

{-
  ARTIFICIAL SIGNS: introduce cancellation into Subset Sum

  The determinant computes Σ over n! permutations in O(n³) using SIGNS.
  The permanent (same sum, no signs) is #P-hard.
  Subset Sum coefficients are all ≥0 (like permanent). No free cancellation.

  IDEA: Replace ∏(1 + x^{wᵢ}) with ∏(1 + αᵢ · x^{wᵢ}) where αᵢ ∈ {±1, ∈ℂ}.
  Then [x^T] = Σ_{S: sum(S)=T} ∏_{i∈S} αᵢ — a SIGNED sum.

  Key insight:
    - For YES (≥1 solution): [x^T] ≠ 0 for RANDOM αᵢ ∈ {±1} (whp if 1 solution)
    - For NO (0 solutions): [x^T] = 0 for ALL αᵢ
  So the signs create a PROBABILISTIC SIGNAL without changing the answer.

  But can they reduce the COMPUTATIONAL COST?

  Experiments:
    1. SIGN EFFECT: [x^T] with various sign patterns
    2. SIGNED DP SPARSITY: does the signed DP table have more zeros?
    3. MONTE CARLO: average |[x^T]|² over random signs → detects YES/NO
    4. PARTIAL SIGNS: evaluate signed P at roots of unity with small modulus
    5. THE FUNDAMENTAL LIMIT: why signs alone can't break the barrier
-}

import qualified Data.IntMap.Strict as IM
import Data.List (foldl')
import Data.Bits (xor, shiftR, testBit)
import PeqNP.ActorSolver (padR)

-- | Signed DP: compute [x^T] of ∏(1 + αᵢ · x^{wᵢ})
-- α is a list of signs (+1 or -1)
-- Returns the signed coefficient at target
signedCoeffAt :: [Int] -> [Int] -> Int -> Int
signedCoeffAt weights signs target =
  let -- DP with signed coefficients: map from sum → signed count
      step :: IM.IntMap Int -> (Int, Int) -> IM.IntMap Int
      step table (w, alpha) =
        IM.foldlWithKey' (\acc s c ->
          let s' = s + w
              c' = alpha * c
          in if s' <= target
             then IM.insertWith (+) s' c' acc
             else acc
        ) table table
      final = foldl' step (IM.singleton 0 1) (zip weights signs)
  in IM.findWithDefault 0 target final

-- | Standard (unsigned) coefficient at target
unsignedCoeffAt :: [Int] -> Int -> Int
unsignedCoeffAt weights target = signedCoeffAt weights (replicate (length weights) 1) target

-- | Count nonzero entries in signed DP table at final level
signedDPSparsity :: [Int] -> [Int] -> Int -> (Int, Int)  -- (nonzero, total_entries)
signedDPSparsity weights signs maxDeg =
  let step table (w, alpha) =
        IM.foldlWithKey' (\acc s c ->
          let s' = s + w
              c' = alpha * c
          in if s' <= maxDeg
             then IM.insertWith (+) s' c' acc
             else acc
        ) table table
      final = foldl' step (IM.singleton 0 1) (zip weights signs)
      -- Remove entries that cancelled to 0
      cleaned = IM.filter (/= 0) final
  in (IM.size cleaned, IM.size final)

-- | Generate deterministic sign pattern from seed
signPattern :: Int -> Int -> [Int]
signPattern n seed = [if testBit (mix (seed + i)) 0 then 1 else -1 | i <- [0..n-1]]
  where mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                     x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
                 in x2 `xor` (x2 `shiftR` 16)

-- | Monte Carlo: average |[x^T]|² over K random sign patterns
-- E[|[x^T]|²] = C(T) (number of solutions!) by orthogonality
monteCarloDetect :: [Int] -> Int -> Int -> (Double, Int)  -- (avg |coeff|², #trials)
monteCarloDetect weights target numTrials =
  let n = length weights
      results = [let signs = signPattern n seed
                     c = signedCoeffAt weights signs target
                 in c * c  -- |c|²
                | seed <- [0..numTrials - 1]]
      avg = fromIntegral (sum results) / fromIntegral numTrials :: Double
  in (avg, numTrials)

-- | Signed evaluation at a root of unity: P_α(ω^j) = ∏(1 + αᵢ · ω^{j·wᵢ})
-- Returns sum over j of P_α(ω^j) · ω^{-jT} / q (= approximate [x^T])
-- Using modular arithmetic (mod prime p, with primitive root ω)
signedModularExtract :: [Int] -> [Int] -> Int -> Int -> Int -> Int
-- weights, signs, target, modulus q, prime p
signedModularExtract weights signs target q p =
  let omega = primitiveRoot p q  -- q-th root of unity mod p
      -- Evaluate P_α(ω^j) for j = 0..q-1
      evalAt j =
        let omJ = modPow omega j p  -- ω^j
        in foldl' (\acc (w, alpha) ->
          let xw = modPow omJ w p  -- (ω^j)^w = ω^{jw}
              factor = (1 + fromIntegral alpha * fromIntegral xw) `mod` p
          in (acc * factor) `mod` p
          ) 1 (zip weights signs)
      -- Inverse DFT: [x^T] ≈ (1/q) Σ_j P(ω^j) · ω^{-jT}
      invQ = modInverse q p
      sumVal = sum [let pj = evalAt j
                        omNeg = modPow omega (q - (j * target `mod` q)) p
                    in (pj * omNeg) `mod` p
                   | j <- [0..q-1]]
  in (sumVal * invQ) `mod` p

-- Modular arithmetic helpers
modPow :: Int -> Int -> Int -> Int
modPow _ 0 _ = 1
modPow b e m
  | even e    = let h = modPow b (e `div` 2) m in (h * h) `mod` m
  | otherwise = (b * modPow b (e - 1) m) `mod` m

modInverse :: Int -> Int -> Int
modInverse a m = modPow a (m - 2) m  -- Fermat's little theorem (m prime)

-- Find a q-th root of unity mod p (p prime, q | p-1)
primitiveRoot :: Int -> Int -> Int
primitiveRoot p q =
  let g = findGenerator p  -- primitive root of F_p
  in modPow g ((p - 1) `div` q) p

findGenerator :: Int -> Int
findGenerator p = head [g | g <- [2..p-1], modPow g (p - 1) p == 1,
                                            modPow g ((p-1) `div` 2) p /= 1]

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
  putStrLn " ARTIFICIAL SIGNS: introduce cancellation into Subset Sum"
  putStrLn " ∏(1 + αᵢ · x^{wᵢ}) — signed generating function"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Effect of signs on [x^T]
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. SIGN EFFECT: [x^T] with 10 random sign patterns ==="
  putStrLn "   YES → should be nonzero (for 1 solution: always ±1)"
  putStrLn "   NO  → should be zero (always, for all patterns)"
  putStrLn ""
  mapM_ (\n -> do
    let (wsY, tY) = mkHashYes n
        (wsN, tN) = mkHash n
        patternsY = [signedCoeffAt wsY (signPattern n s) tY | s <- [0..9]]
        patternsN = [signedCoeffAt wsN (signPattern n s) tN | s <- [0..9]]
    putStrLn $ "  n=" ++ show n ++ " YES: " ++ show patternsY
      ++ " (unsigned=" ++ show (unsignedCoeffAt wsY tY) ++ ")"
    putStrLn $ "  n=" ++ show n ++ " NO:  " ++ show patternsN
      ++ " (unsigned=" ++ show (unsignedCoeffAt wsN tN) ++ ")"
    putStrLn ""
    ) [6, 8, 10]

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Signed DP table sparsity
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. SIGNED DP SPARSITY: more zeros in signed table? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "unsigned" ++ padR 12 "signed-1"
    ++ padR 12 "signed-2" ++ padR 12 "signed-3"
  putStrLn (replicate 54 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (unsNZ, _) = signedDPSparsity ws (replicate n 1) t
        (s1NZ, _) = signedDPSparsity ws (signPattern n 42) t
        (s2NZ, _) = signedDPSparsity ws (signPattern n 137) t
        (s3NZ, _) = signedDPSparsity ws (signPattern n 999) t
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show unsNZ)
      ++ padR 12 (show s1NZ)
      ++ padR 12 (show s2NZ)
      ++ padR 12 (show s3NZ)
    ) [6, 8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Monte Carlo detection
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. MONTE CARLO: E[|[x^T]|²] over random signs ==="
  putStrLn "   E[|c|²] = C(T) = # solutions (by orthogonality!)"
  putStrLn "   So: avg > 0 → YES, avg = 0 → NO"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 12 "E[|c|²]"
    ++ padR 10 "trials" ++ padR 12 "unsigned" ++ padR 10 "verdict"
  putStrLn (replicate 56 '-')
  mapM_ (\n -> do
    let k = 50
    -- YES
    let (wsY, tY) = mkHashYes n
        (avgY, _) = monteCarloDetect wsY tY k
        unsY = unsignedCoeffAt wsY tY
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 12 (showF 2 avgY)
      ++ padR 10 (show k)
      ++ padR 12 (show unsY)
      ++ padR 10 (if avgY > 0.5 then "YES" else "NO")
    -- NO
    let (wsN, tN) = mkHash n
        (avgN, _) = monteCarloDetect wsN tN k
        unsN = unsignedCoeffAt wsN tN
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 12 (showF 2 avgN)
      ++ padR 10 (show k)
      ++ padR 12 (show unsN)
      ++ padR 10 (if avgN > 0.5 then "YES" else "NO")
    ) [6, 8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: Cost analysis — signs don't reduce work
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. COST: signed vs unsigned DP operations ==="
  putStrLn "   (both O(n × T) — signs change VALUES not COST)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "target" ++ padR 12 "n×T"
    ++ padR 12 "2^n" ++ padR 12 "ratio"
  putStrLn (replicate 54 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        cost = n * t
        expn = (2::Int)^n
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show t)
      ++ padR 12 (show cost)
      ++ padR 12 (show expn)
      ++ padR 12 (showF 1 (fromIntegral cost / fromIntegral expn :: Double))
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: The mathematical identity
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. THE IDENTITY: E[|[x^T]|²] = C(T) exactly ==="
  putStrLn "   Proof: E[∏αᵢ · ∏αⱼ] = E[∏α²] = 1 if S=S', 0 if S≠S'"
  putStrLn "   So E[|c|²] = Σ_{S:sum=T} 1 = C(T)"
  putStrLn ""
  putStrLn "   This means: signs give PERFECT detection in expectation."
  putStrLn "   BUT each trial costs O(n × T) — pseudo-polynomial."
  putStrLn "   For density-1: T ≈ n·2^n, so each trial is O(n²·2^n)."
  putStrLn "   One trial suffices (if C(T)≥1, E[|c|²]≥1), but that"
  putStrLn "   one trial already costs exponential time."
  putStrLn ""
  putStrLn "   The cancellation is PERFECT for detection (no false positives"
  putStrLn "   or negatives). The barrier is not information — it's COMPUTATION."
  putStrLn "   We know EXACTLY what to compute. We just can't compute it fast."
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "INSIGHT:"
  putStrLn " Signs give PERFECT CANCELLATION for Subset Sum detection."
  putStrLn " E[|[x^T]|²] = C(T) — the exact solution count, for FREE."
  putStrLn " The problem is NOT information-theoretic — it's computational."
  putStrLn ""
  putStrLn " This means: IF a poly-time algorithm exists, it must find a way"
  putStrLn " to compute [x^T]∏(1+αᵢx^{wᵢ}) WITHOUT expanding all n×T terms."
  putStrLn " The STRUCTURE of the product (factored form) must be exploitable."
  putStrLn ""
  putStrLn " ∏(1+αᵢx^{wᵢ}) is a product of n SPARSE polynomials (2 terms each)."
  putStrLn " The product has 2^n terms. Can we extract ONE coefficient of a"
  putStrLn " product of n binomials in less than O(n×T) time?"
  putStrLn " THAT is the exact mathematical question P vs NP reduces to."
  putStrLn "═══════════════════════════════════════════════════════════════════"
