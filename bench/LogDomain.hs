module Main where

{-
  THE LOG DOMAIN: working with log P(x) instead of P(x)

  P(x) = ∏(1 + x^{w_i})  — dense, 2^n coefficients
  log P(x) = Σ log(1 + x^{w_i}) = Σ_i Σ_j (-1)^{j+1} x^{j·w_i} / j  — SPARSE

  The log is sparse because only multiples of w_i contribute.
  Total nonzero terms in log P: at most Σ_i floor(T / w_i).
  For density-1 (w_i ≈ 2^n, T ≈ n·2^{n-1}): each w_i has ~n/2 multiples ≤ T.
  Total terms: n × n/2 = O(n²). POLYNOMIAL!

  Then: [x^T] P(x) = [x^T] exp(log P(x))

  The exp of a power series f with f(0)=0 can be computed via:
    [x^0] exp(f) = 1
    [x^r] exp(f) = (1/r) Σ_{k=1}^{r} k·[x^k]f · [x^{r-k}]exp(f)

  If we only compute coefficients at positions we NEED, and f is sparse
  (most [x^k]f = 0), maybe the recursion shortcuts?

  EXPERIMENT:
  1. Build log P(x) as a sparse polynomial (map from exponent → rational coefficient)
  2. Compute [x^T] exp(log P) using the recursion, tracking how many
     nonzero terms of f actually participate
  3. Measure: how many operations to reach [x^T]?
  4. Compare with brute force 2^n
-}

import qualified Data.Map.Strict as Map
import Data.List (foldl')
import Data.Bits (xor, shiftR, testBit)
import qualified Data.Set as Set
import PeqNP.ActorSolver (padR)

-- | Sparse polynomial: map from exponent → coefficient (as Double for speed)
type SparsePoly = Map.Map Int Double

-- | Build log P(x) = Σ_i Σ_{j=1}^{maxJ} (-1)^{j+1}/j × x^{j·w_i}
-- Only include terms where j·w_i ≤ maxDeg
buildLogP :: [Int] -> Int -> SparsePoly
buildLogP weights maxDeg =
  foldl' (\acc w ->
    let terms = takeWhile (\(e,_) -> e <= maxDeg)
                  [(j * w, (-1) ** fromIntegral (j+1) / fromIntegral j)
                  | j <- [1..maxDeg `div` max 1 w]]
    in foldl' (\m (e, c) -> Map.insertWith (+) e c m) acc terms
  ) Map.empty weights

-- | Count nonzero terms in the sparse log polynomial
logPStats :: SparsePoly -> (Int, Int, Int)  -- (nonzero_terms, min_exp, max_exp)
logPStats sp =
  let keys = Map.keys sp
  in (Map.size sp,
      if null keys then 0 else minimum keys,
      if null keys then 0 else maximum keys)

-- | Compute [x^r] exp(f) using the Newton recursion.
-- [x^0] exp(f) = 1  (when f(0) = 0)
-- [x^r] exp(f) = (1/r) Σ_{k=1}^{r} k · [x^k]f · [x^{r-k}]exp(f)
--
-- We compute ALL coefficients 0..target.
-- Returns: (coefficient at target, total_ops, coefficients_computed)
expCoefficient :: SparsePoly -> Int -> (Double, Int, Int)
expCoefficient logP target =
  let -- Get the nonzero positions of logP for fast iteration
      logPList = Map.toAscList logP
      -- Build exp coefficients iteratively
      (expCoeffs, ops) = foldl' (\(coeffs, opCount) r ->
        -- [x^r] exp(f) = (1/r) Σ_{k: [x^k]f ≠ 0, k ≤ r} k · [x^k]f · coeffs[r-k]
        let terms = [(k, c) | (k, c) <- logPList, k <= r, k > 0]
            sumVal = sum [fromIntegral k * c * Map.findWithDefault 0 (r - k) coeffs
                         | (k, c) <- terms]
            newCoeff = sumVal / fromIntegral r
        in (Map.insert r newCoeff coeffs, opCount + length terms)
        ) (Map.singleton 0 1.0, 0) [1..target]
  in (Map.findWithDefault 0 target expCoeffs, ops, Map.size expCoeffs)

-- | LAZY version: only compute coefficients that are "reachable" from
-- the nonzero terms of logP. If logP has terms at positions {p₁, p₂, ...},
-- then [x^r]exp(f) depends only on [x^{r-p}]exp(f) for p in {p₁, p₂, ...}.
-- So we only need coefficients at positions reachable by subtracting logP exponents.
--
-- Starting from target T, work backwards:
--   Need [x^T]exp → needs [x^{T-p}]exp for each p in logP positions
--   Need [x^{T-p}]exp → needs [x^{T-p-q}]exp for each q in logP positions
--   ...until we reach [x^0]exp = 1
--
-- The set of needed positions = {T - Σ aᵢpᵢ : aᵢ ≥ 0, sum ≥ 0}
-- This is the set of non-negative integers reachable by SUBTRACTING
-- multiples of logP positions from T.
--
-- For sparse logP: this set might be MUCH smaller than {0..T}!
neededPositions :: SparsePoly -> Int -> Set.Set Int
neededPositions logP target =
  let positions = Map.keys logP
      -- BFS from target backwards
      go visited [] = visited
      go visited queue =
        let new = [ r - p
                  | r <- queue
                  , p <- positions
                  , p > 0
                  , r - p >= 0
                  , not (Set.member (r - p) visited)
                  ]
            newSet = Set.fromList new
            visited' = Set.union visited newSet
        in go visited' (Set.toList newSet)
  in go (Set.singleton target) [target]

-- | Compute exp coefficient using ONLY needed positions
expCoefficientLazy :: SparsePoly -> Int -> (Double, Int, Int)
expCoefficientLazy logP target =
  let needed = neededPositions logP target
      logPList = Map.toAscList logP
      -- Only compute coefficients at needed positions, in order
      neededList = Set.toAscList needed
      (expCoeffs, ops) = foldl' (\(coeffs, opCount) r ->
        if r == 0 then (Map.insert 0 1.0 coeffs, opCount)
        else
          let terms = [(k, c) | (k, c) <- logPList, k <= r, k > 0]
              sumVal = sum [fromIntegral k * c * Map.findWithDefault 0 (r - k) coeffs
                           | (k, c) <- terms]
              newCoeff = sumVal / fromIntegral r
          in (Map.insert r newCoeff coeffs, opCount + length terms)
        ) (Map.empty, 0) neededList
  in (Map.findWithDefault 0 target expCoeffs, ops, Map.size expCoeffs)

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
  putStrLn " THE LOG DOMAIN: sparse log, dense exp"
  putStrLn " Can we stay in log-land and avoid the 2^n?"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: How sparse is log P?
  putStrLn "=== SPARSITY OF log P(x) ==="
  putStrLn (padR 5 "n" ++ padR 12 "target" ++ padR 14 "logP-terms"
    ++ padR 10 "n²" ++ padR 12 "ratio")
  putStrLn (replicate 55 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        logP = buildLogP ws t
        (terms, _, _) = logPStats logP
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show t)
      ++ padR 14 (show terms)
      ++ padR 10 (show (n*n))
      ++ padR 12 (showF 1 (fromIntegral terms / fromIntegral (n*n) :: Double))
    ) [6, 8, 10, 12]
  putStrLn ""

  -- Part 2: Needed positions (lazy) vs full range
  putStrLn "=== LAZY: how many positions does exp actually need? ==="
  putStrLn (padR 5 "n" ++ padR 12 "target" ++ padR 14 "needed-pos"
    ++ padR 14 "full-range" ++ padR 12 "ratio")
  putStrLn (replicate 58 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        logP = buildLogP ws t
        needed = neededPositions logP t
        numNeeded = Set.size needed
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show t)
      ++ padR 14 (show numNeeded)
      ++ padR 14 (show t)
      ++ padR 12 (showF 4 (fromIntegral numNeeded / fromIntegral t :: Double))
    ) [6, 8, 10]
  putStrLn ""

  -- Part 3: Does the exp coefficient detect achievability?
  putStrLn "=== CORRECTNESS: does [x^T]exp(logP) detect YES/NO? ==="
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        -- NO target (standard)
        logPno = buildLogP ws t
        (coeffNo, opsNo, posNo) = expCoefficientLazy logPno t
        -- YES target (sum of first half)
        tYes = sum (take (n `div` 2) ws)
        logPyes = buildLogP ws tYes
        (coeffYes, opsYes, posYes) = expCoefficientLazy logPyes tYes
        -- Ground truth
        dpNo = Set.member t (dpReachable ws)
        dpYes = Set.member tYes (dpReachable ws)
    putStrLn $ "  n=" ++ show n ++ " NO-target:"
      ++ " coeff=" ++ showF 4 coeffNo
      ++ " (expect 0, DP=" ++ show dpNo ++ ")"
      ++ " ops=" ++ show opsNo ++ " pos=" ++ show posNo
    putStrLn $ "  n=" ++ show n ++ " YES-target:"
      ++ " coeff=" ++ showF 4 coeffYes
      ++ " (expect ≥1, DP=" ++ show dpYes ++ ")"
      ++ " ops=" ++ show opsYes ++ " pos=" ++ show posYes
    putStrLn ""
    ) [6, 8, 10]

  -- Part 4: The key scaling question
  putStrLn "=== SCALING: needed positions vs n ==="
  putStrLn (padR 5 "n" ++ padR 14 "needed" ++ padR 14 "2^n"
    ++ padR 14 "needed/2^n" ++ padR 14 "needed/n²")
  putStrLn (replicate 62 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        logP = buildLogP ws t
        needed = neededPositions logP t
        numN = Set.size needed
        twoN = (2::Int)^n
    putStrLn $ padR 5 (show n)
      ++ padR 14 (show numN)
      ++ padR 14 (show twoN)
      ++ padR 14 (showF 4 (fromIntegral numN / fromIntegral twoN :: Double))
      ++ padR 14 (showF 1 (fromIntegral numN / fromIntegral (n*n) :: Double))
    ) [6, 8, 10, 12]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn "If needed positions grow as poly(n) → POLYNOMIAL ALGORITHM"
  putStrLn "If needed positions grow as 2^n → same as brute force"
  putStrLn "═══════════════════════════════════════════════════════════"

-- Simple DP reachable for verification
dpReachable :: [Int] -> Set.Set Int
dpReachable = foldl' (\acc w -> Set.union acc (Set.map (+w) acc)) (Set.singleton 0)

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int) / fromIntegral factor :: Double
  in show rounded
