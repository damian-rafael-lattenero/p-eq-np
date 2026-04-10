module Main where

{-
  THE MUTATING ORACLE EXPERIMENT

  The generating function for suffix [d..n-1] is:
    P_d(x) = ∏_{i=d}^{n-1} (1 + x^{w_i})

  [x^r]P_d(x) > 0  ⟺  r is achievable by the suffix.

  KEY INSIGHT: P_d evaluated at a SINGLE point α is:
    P_d(α) = ∏_{i=d}^{n-1} (1 + α^{w_i})

  This is ONE NUMBER that encodes information about ALL coefficients.
  It "mutates" at each depth: P_{d-1}(α) = (1 + α^{w_d}) × P_d(α)

  We can track P_d(α) for MULTIPLE evaluation points α₁, α₂, ...
  Each is O(1) to update per step. K points = O(K) per step.

  The question: with K = poly(n) evaluation points, can we
  determine [x^r]P(x) ≠ 0?

  EXPERIMENT: evaluate P at K random points in Z_p (finite field).
  Track how many points "agree" that r is achievable vs not.
  Compare with ground truth.

  If K = O(n²) evaluation points suffice → polynomial algorithm!
-}

import Data.List (foldl')
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- | Modular exponentiation: a^b mod m
modPow :: Integer -> Integer -> Integer -> Integer
modPow _ 0 m = 1 `mod` m
modPow a b m
  | even b    = let half = modPow a (b `div` 2) m
                in (half * half) `mod` m
  | otherwise = (a * modPow a (b - 1) m) `mod` m

-- | Evaluate the generating function P(α) = ∏(1 + α^{w_i}) mod p
-- for suffix [d..n-1], at the evaluation point α, in field Z_p.
-- Returns the product as a single number in Z_p.
evalGenFunc :: Integer -> Integer -> [Integer] -> Integer
evalGenFunc p alpha weights =
  foldl' (\acc w -> (acc * ((1 + modPow alpha w p) `mod` p)) `mod` p) 1 weights

-- | Build suffix evaluations bottom-up.
-- Returns list of P_d(α) for d = 0, 1, ..., n.
-- P_n(α) = 1 (empty product). P_d(α) = (1 + α^{w_d}) × P_{d+1}(α).
suffixEvals :: Integer -> Integer -> [Integer] -> [Integer]
suffixEvals p alpha weights =
  let n = length weights
      -- Process from right to left
      evals = scanr (\w acc -> (acc * ((1 + modPow alpha (fromIntegral w) p) `mod` p)) `mod` p)
                    1 (map fromIntegral weights)
  in evals  -- length n+1: evals[d] = P_d(α)

-- | For the DFT approach: [x^r]P(x) = (1/N) Σ_{j=0}^{N-1} P(ω^j) × ω^{-jr}
-- where ω is a primitive N-th root of unity mod p.
--
-- We use p where p-1 is divisible by N, so ω = g^((p-1)/N) where g is a generator.
--
-- If [x^r]P = 0, the sum equals 0 (mod p).
-- If [x^r]P ≠ 0, the sum equals [x^r]P × N ≠ 0 (mod p, assuming p > [x^r]P).
--
-- For density-1: [x^r]P ∈ {0, 1}. So the sum is either 0 or N.
-- We can distinguish these if N < p.
--
-- BUT: we need N > degree(P) for exact extraction. With N < degree(P),
-- we get the aliased coefficient (same as modular oracle).
--
-- EXPERIMENT: use small N (polynomial) and see how the aliased
-- coefficient behaves. Does it distinguish achievable from not?

-- | Find a primitive root mod p (brute force, p must be prime).
primitiveRoot :: Integer -> Integer
primitiveRoot p = head [g | g <- [2..p-1], isPrimRoot g p]
  where
    isPrimRoot g q = all (\e -> modPow g ((q-1) `div` e) q /= 1) (primeFactors (q-1))
    primeFactors n = go n 2
      where
        go 1 _ = []
        go m f
          | f * f > m = [m]
          | m `mod` f == 0 = f : go (divAll m f) (f+1)
          | otherwise = go m (f+1)
        divAll m f
          | m `mod` f == 0 = divAll (m `div` f) f
          | otherwise = m

-- | Compute aliased coefficient: Σ_{k ≡ r (mod N)} [x^k]P(x)
-- Using N evaluation points: P(ω^0), P(ω^1), ..., P(ω^{N-1})
-- Result = (1/N) Σ_j P(ω^j) × ω^{-jr}  (mod p)
aliasedCoeff :: Integer -> Integer -> Int -> [Int] -> Integer
aliasedCoeff p omega n_eval weights =
  let r_target = fromIntegral (sum weights `div` 2 + 1) :: Integer
      -- Evaluate P(ω^j) for j = 0..N-1
      evals = [ evalGenFunc p (modPow omega (fromIntegral j) p) (map fromIntegral weights)
              | j <- [0..n_eval - 1] ]
      -- Compute Σ P(ω^j) × ω^{-jr}
      nInv = modPow (fromIntegral n_eval) (p - 2) p  -- modular inverse of N
      sumVal = foldl' (\acc (j, pj) ->
        let phase = modPow omega ((p - 1 - ((fromIntegral j * r_target) `mod` (p-1))) `mod` (p-1)) p
        in (acc + pj * phase) `mod` p
        ) 0 (zip [0 :: Int ..] evals)
  in (sumVal * nInv) `mod` p

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " MUTATING ORACLE: generating function as state"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: Single-point evaluation as oracle
  -- Can P(α) for a single α tell us about achievability?
  putStrLn "=== P(α) at random points: achievable vs non-achievable target ==="
  let p = 104729  -- large prime
      g = primitiveRoot p
  putStrLn $ "  Using field Z_" ++ show p ++ ", generator=" ++ show g
  putStrLn ""

  -- Test: for each n, evaluate P(α) at several random points
  -- for both YES target and NO target. Do the values differ?
  putStrLn (padR 5 "n" ++ padR 10 "target" ++ padR 10 "P(α₁)" ++ padR 10 "P(α₂)"
    ++ padR 10 "P(α₃)" ++ padR 10 "achiev?")
  putStrLn (replicate 55 '-')

  mapM_ (\n -> do
    let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                     x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
                 in x2 `xor` (x2 `shiftR` 16)
        ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
             | i <- [0..n-1 :: Int]]
        tNo  = sum ws `div` 2 + 1        -- NO target
        tYes = sum (take (n `div` 2) ws)  -- YES target

        alpha1 = modPow g 1 p
        alpha2 = modPow g 7 p
        alpha3 = modPow g 13 p

        evalAt a t_target wsI = evalGenFunc p a (map fromIntegral wsI)

    -- NO target
    putStrLn $ padR 5 (show n)
      ++ padR 10 "NO"
      ++ padR 10 (show (evalAt alpha1 tNo ws))
      ++ padR 10 (show (evalAt alpha2 tNo ws))
      ++ padR 10 (show (evalAt alpha3 tNo ws))
      ++ padR 10 "NO"

    -- YES target
    putStrLn $ padR 5 (show n)
      ++ padR 10 "YES"
      ++ padR 10 (show (evalAt alpha1 tYes ws))
      ++ padR 10 (show (evalAt alpha2 tYes ws))
      ++ padR 10 (show (evalAt alpha3 tYes ws))
      ++ padR 10 "YES"
    putStrLn ""
    ) [8, 10, 12, 14]

  -- Part 2: The mutation in action — how P_d(α) evolves
  putStrLn "=== THE MUTATION: P_d(α) at each depth (n=12) ==="
  let n12 = 12 :: Int
      mix12 x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                     x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
                 in x2 `xor` (x2 `shiftR` 16)
      ws12 = [2^n12 + (abs (mix12 (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n12-1)))
             | i <- [0..n12-1]]
      evals12 = suffixEvals p (modPow g 1 p) (map fromIntegral ws12)
  putStrLn $ "  weights=" ++ show (take 6 ws12) ++ "..."
  putStrLn $ "  depth:  " ++ concatMap (\i -> padR 10 (show i)) [0..n12]
  putStrLn $ "  P_d(α): " ++ concatMap (\v -> padR 10 (show v)) evals12
  putStrLn ""
  putStrLn "  ^ Each value = prev × (1 + α^{w_d}) mod p"
  putStrLn "  The oracle MUTATES at each depth — one multiply per step."
  putStrLn ""

  -- Part 3: Aliased DFT with small N
  putStrLn "=== ALIASED DFT: can small N distinguish YES from NO? ==="
  putStrLn (padR 5 "n" ++ padR 8 "N" ++ padR 14 "alias(NO)" ++ padR 14 "alias(YES)"
    ++ padR 10 "differ?")
  putStrLn (replicate 55 '-')

  -- Use p = 65537 (Fermat prime, has nice roots of unity)
  let pF = 65537 :: Integer
      gF = primitiveRoot pF

  mapM_ (\(n, nEval) -> do
    let mix' x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                      x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
                  in x2 `xor` (x2 `shiftR` 16)
        ws = [2^n + (abs (mix' (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
             | i <- [0..n-1 :: Int]]

        -- Root of unity of order nEval
        omega = modPow gF ((pF - 1) `div` fromIntegral nEval) pF

        aliasNo  = aliasedCoeff pF omega nEval ws
        -- For YES: use a different target extraction
        -- Actually aliasedCoeff uses sum/2+1 internally, let's compute both
        tNo = sum ws `div` 2 + 1
        tYes = sum (take (n `div` 2) ws)

    putStrLn $ padR 5 (show n)
      ++ padR 8 (show nEval)
      ++ padR 14 (show aliasNo)
      ++ padR 14 "—"
      ++ padR 10 (if aliasNo == 0 then "PRUNED!" else "pass")
    ) [ (10, 16), (10, 32), (10, 64), (10, 128), (10, 256)
      , (12, 16), (12, 64), (12, 256)
      , (14, 16), (14, 64), (14, 256) ]

  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn "If alias(NO) = 0 consistently → the DFT detects"
  putStrLn "non-achievability with just N evaluations (polynomial!)"
  putStrLn "═══════════════════════════════════════════════════════════"
