module Main where

-- THE COMPRESSION GAP: searching for the holy grail
--
-- For each NO-instance: what is the SMALLEST modulus M such that
-- the modular DP correctly rejects T?
--
-- If min-M = O(poly(n)) for all instances → poly compression exists → P=NP
-- If min-M = O(2^n) → no poly compression → evidence for P≠NP
--
-- Also: try MULTI-MODULAR compression (M₁ × M₂ × ...) — the torus.
-- And: try NON-STANDARD compressions (intervals, mixed, hash-based).
--
-- This is the most direct experimental attack on P vs NP possible.

import qualified Data.IntSet as IS
import Data.List (foldl', sort)
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- | Reachable residues mod M
reachableModM :: [Int] -> Int -> IS.IntSet
reachableModM weights m =
  foldl' (\acc w ->
    IS.union acc (IS.map (\r -> (r + w) `mod` m) acc)
  ) (IS.singleton 0) weights

-- | Does modulus M correctly reject this NO target?
rejectsTarget :: [Int] -> Int -> Int -> Bool
rejectsTarget weights target m =
  not (IS.member (target `mod` m) (reachableModM weights m))

-- | Find minimum single modulus that rejects target (brute force search)
minRejectingModulus :: [Int] -> Int -> Int -> Maybe Int
minRejectingModulus weights target maxM =
  case filter (rejectsTarget weights target) [2..maxM] of
    []    -> Nothing
    (m:_) -> Just m

-- | Multi-modular: does the pair (M₁, M₂) reject target?
-- Target is rejected if (T mod M₁, T mod M₂) is NOT in the
-- reachable set on torus Z/M₁ × Z/M₂
pairRejectsTarget :: [Int] -> Int -> Int -> Int -> Bool
pairRejectsTarget weights target m1 m2 =
  let tPair = (target `mod` m1, target `mod` m2)
      reachable = foldl' (\acc w ->
        let wPair = (w `mod` m1, w `mod` m2)
        in IS.foldl' (\a encoded ->
          let (r1, r2) = decode m2 encoded
              new = encode m2 ((r1 + fst wPair) `mod` m1) ((r2 + snd wPair) `mod` m2)
          in IS.insert new a
          ) acc acc
        ) (IS.singleton (encode m2 0 0)) weights
  in not (IS.member (encode m2 (fst tPair) (snd tPair)) reachable)
  where
    encode m2' a b = a * m2' + b
    decode m2' x = (x `div` m2', x `mod` m2')

-- | Triple modular: (M₁, M₂, M₃)
tripleRejectsTarget :: [Int] -> Int -> Int -> Int -> Int -> Bool
tripleRejectsTarget weights target m1 m2 m3 =
  let tTrip = encode (target `mod` m1) (target `mod` m2) (target `mod` m3)
      reachable = foldl' (\acc w ->
        IS.foldl' (\a enc ->
          let (r1, r2, r3) = decode enc
              new = encode ((r1 + w `mod` m1) `mod` m1)
                          ((r2 + w `mod` m2) `mod` m2)
                          ((r3 + w `mod` m3) `mod` m3)
          in IS.insert new a
          ) acc acc
        ) (IS.singleton (encode 0 0 0)) weights
  in not (IS.member tTrip reachable)
  where
    encode a b c = a * (m2 * m3) + b * m3 + c
    decode x = (x `div` (m2 * m3), (x `mod` (m2 * m3)) `div` m3, x `mod` m3)

-- | Interval compression: track s `div` d instead of s
-- Correctly rejects if no reachable sum falls in [T-d+1, T+d-1]
intervalRejects :: [Int] -> Int -> Int -> Bool
intervalRejects weights target d =
  let tBucket = target `div` d
      reachable = foldl' (\acc w ->
        IS.union acc (IS.map (\s -> (s + w) `div` d) (IS.filter (\s -> s * d + w <= target + d) acc))
        ) (IS.singleton 0) weights
      -- Actually, simpler: compute exact reachable, check if any is in [T-d+1..T+d-1]
      exactReachable = foldl' (\acc w -> IS.union acc (IS.map (+w) acc)) (IS.singleton 0) weights
  in IS.null (IS.filter (\s -> abs (s - target) < d) exactReachable)

-- | Combined: modular M AND interval d
combinedRejects :: [Int] -> Int -> Int -> Int -> Bool
combinedRejects weights target m d =
  rejectsTarget weights target m || intervalRejects weights target d

-- | Exact check: is target truly unreachable?
exactCheck :: [Int] -> Int -> Bool
exactCheck weights target =
  not $ IS.member target $ foldl' (\acc w -> IS.union acc (IS.map (+w) acc)) (IS.singleton 0) weights

mkHash :: Int -> ([Int], Int)
mkHash n =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
           | i <- [0..n-1 :: Int]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

-- | Generate VERIFIED NO instance (check that target is indeed unreachable)
mkVerifiedNo :: Int -> Maybe ([Int], Int)
mkVerifiedNo n =
  let (ws, t) = mkHash n
  in if exactCheck ws t then Just (ws, t) else Nothing

-- Multiple NO targets: try several near sum/2
mkNoTargets :: Int -> [([Int], Int)]
mkNoTargets n =
  let (ws, _) = mkHash n
      totalSum = sum ws
      candidates = [totalSum `div` 2 + delta | delta <- [1, -1, 2, -2, 3, -3, 5, -5, 7, -7]]
      verified = filter (\t -> exactCheck ws t) candidates
  in [(ws, t) | t <- take 3 verified]

smallPrimes :: [Int]
smallPrimes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
               101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,
               197,199,211,223,227,229,233,239,241,251]

showF :: Int -> Double -> String
showF d x = let f = 10 ^ d :: Int
                r = fromIntegral (round (x * fromIntegral f) :: Int) / fromIntegral f :: Double
            in show r

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn " THE COMPRESSION GAP: poly AND correct — does it exist?"
  putStrLn " For each NO-instance: what's the smallest M that rejects T?"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Single modulus — minimum rejecting M
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. MIN SINGLE MODULUS: smallest M that rejects T ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "target" ++ padR 10 "min-M"
    ++ padR 10 "n²" ++ padR 10 "2^(n/2)" ++ padR 8 "exact"
  putStrLn (replicate 56 '-')
  mapM_ (\n -> do
    let noInsts = mkNoTargets n
    case noInsts of
      [] -> putStrLn $ padR 5 (show n) ++ "  (no verified NO instance found)"
      ((ws, t):_) -> do
        let minM = minRejectingModulus ws t 500
            isNo = exactCheck ws t
        putStrLn $ padR 5 (show n)
          ++ padR 12 (show t)
          ++ padR 10 (maybe ">500" show minM)
          ++ padR 10 (show (n*n))
          ++ padR 10 (show ((2::Int)^(n `div` 2)))
          ++ padR 8 (if isNo then "NO" else "YES!")
    ) [6, 7, 8, 9, 10, 11, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Pair modular — does (M₁,M₂) help?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. PAIR MODULAR: does a 2D torus reject better? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "target" ++ padR 8 "M₁" ++ padR 8 "M₂"
    ++ padR 10 "M₁×M₂" ++ padR 8 "reject"
  putStrLn (replicate 52 '-')
  mapM_ (\n -> do
    let noInsts = mkNoTargets n
    case noInsts of
      [] -> putStrLn $ padR 5 (show n) ++ "  (no NO instance)"
      ((ws, t):_) -> do
        -- Try several prime pairs
        let pairs = [(p1, p2) | p1 <- take 10 smallPrimes,
                                p2 <- take 10 (drop 10 smallPrimes),
                                p1 < p2, gcd p1 p2 == 1]
            results = [(p1, p2, pairRejectsTarget ws t p1 p2) | (p1, p2) <- take 20 pairs]
            firstReject = filter (\(_, _, r) -> r) results
        case firstReject of
          [] -> putStrLn $ padR 5 (show n) ++ padR 12 (show t) ++ "  none of 20 pairs reject"
          ((p1, p2, _):_) ->
            putStrLn $ padR 5 (show n) ++ padR 12 (show t)
              ++ padR 8 (show p1) ++ padR 8 (show p2)
              ++ padR 10 (show (p1*p2))
              ++ padR 8 "YES!"
    ) [6, 7, 8, 9, 10, 11, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Exhaustive search — what compression TYPE works?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. COMPRESSION SEARCH: which types reject for n=8? ==="
  putStrLn ""
  let noInsts8 = mkNoTargets 8
  case noInsts8 of
    [] -> putStrLn "  No verified NO instance at n=8"
    ((ws8, t8):_) -> do
      putStrLn $ "  Instance: n=8, T=" ++ show t8
      -- Single modulus
      let singleResult = minRejectingModulus ws8 t8 1000
      putStrLn $ "  Single modulus (M ≤ 1000): " ++ maybe "NONE" (\m -> "M=" ++ show m) singleResult
      -- Pair modulus
      let pairResults = [(p1, p2) | p1 <- take 15 smallPrimes,
                                     p2 <- drop 15 (take 30 smallPrimes),
                                     gcd p1 p2 == 1,
                                     pairRejectsTarget ws8 t8 p1 p2]
      putStrLn $ "  Pair modulus: " ++ (if null pairResults then "NONE" else show (head pairResults))
      -- Triple
      let tripleResults = [(p1,p2,p3) | p1 <- [3,5,7], p2 <- [11,13,17], p3 <- [19,23,29],
                                         tripleRejectsTarget ws8 t8 p1 p2 p3]
      putStrLn $ "  Triple modulus: " ++ (if null tripleResults then "NONE" else show (head tripleResults))
      -- Saturation check
      let satCheck m = IS.size (reachableModM ws8 m)
      putStrLn $ "  Saturation: mod 97 → " ++ show (satCheck 97) ++ "/97"
        ++ ", mod 251 → " ++ show (satCheck 251) ++ "/251"
        ++ ", mod 997 → " ++ show (satCheck 997) ++ "/997"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: THE CRITICAL QUESTION — min-M scaling
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. SCALING: min rejecting M vs n ==="
  putStrLn "   min-M / n² → const : POLY COMPRESSION EXISTS (P=NP!)"
  putStrLn "   min-M / 2^n → const : same as exact (P≠NP evidence)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "min-M" ++ padR 10 "n²" ++ padR 10 "M/n²"
    ++ padR 12 "2^(n/2)" ++ padR 12 "M/2^(n/2)"
  putStrLn (replicate 60 '-')
  mapM_ (\n -> do
    let noInsts = mkNoTargets n
    case noInsts of
      [] -> putStrLn $ padR 5 (show n) ++ "  (no NO instance — target is reachable)"
      ((ws, t):_) -> do
        let minM = minRejectingModulus ws t 2000
            halfN = (2::Int)^(n `div` 2)
        case minM of
          Nothing -> putStrLn $ padR 5 (show n) ++ padR 10 ">2000"
            ++ padR 10 (show (n*n)) ++ padR 10 "—"
            ++ padR 12 (show halfN) ++ padR 12 "—"
          Just m -> putStrLn $ padR 5 (show n) ++ padR 10 (show m)
            ++ padR 10 (show (n*n))
            ++ padR 10 (showF 2 (fromIntegral m / fromIntegral (n*n) :: Double))
            ++ padR 12 (show halfN)
            ++ padR 12 (showF 4 (fromIntegral m / fromIntegral halfN :: Double))
    ) [6, 7, 8, 9, 10, 11, 12, 13, 14]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "THE VERDICT:"
  putStrLn " If min-M grows POLYNOMIALLY with n:"
  putStrLn "   → A poly-size compression EXISTS for every NO-instance"
  putStrLn "   → Combined with YES-certificate (subset), this gives P = NP"
  putStrLn ""
  putStrLn " If min-M grows EXPONENTIALLY with n:"
  putStrLn "   → No poly-size modular compression can certify NO"
  putStrLn "   → Strong evidence that P ≠ NP (at least for modular proofs)"
  putStrLn ""
  putStrLn " Note: even if MODULAR compression fails, some OTHER compression"
  putStrLn " might work. But modular is the most structured option we have."
  putStrLn "═══════════════════════════════════════════════════════════════════"
