module Main where

-- DYNAMIC RICH CATALOG: O(n/log n) primes + O(1) compatibility via hash
--
-- Fixes two issues from RichCatalog:
-- 1. Compatible pairs were computed O(sigs²) — now O(sigs) via hash lookup
-- 2. Fixed 8 primes saturate at n>55 — now dynamic prime count scales with n
--
-- Dynamic primes: use first k primes where ∏pᵢ > 2^{n/2}.
-- By prime number theorem: k ≈ n/(2 ln(n)) primes suffice.
-- Oracle cost: O(n × Σpᵢ) = O(n² × max_prime) = O(n² × n log n) = O(n³ log n)
--
-- Hash-based matching: instead of checking all L×R sig pairs,
-- for each LEFT sig, compute the REQUIRED right sig and hash-lookup.
-- Cost: O(|left_sigs|) = O(2^{n/2}) — same as MITM but with pruning.
--
-- TOTAL COST: O(2^{n/2}) enum + O(n³ log n) oracle + O(2^{n/2}) match
-- = O(2^{n/2}) dominated. Same as MITM asymptotically but with
-- massive constant-factor reduction from pruning.

import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import Data.List (foldl')
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- | Generate first k primes
firstKPrimes :: Int -> [Int]
firstKPrimes k = take k primesList
  where
    primesList = sieve [2..]
    sieve (p:xs) = p : sieve [x | x <- xs, x `mod` p /= 0]
    sieve [] = []

-- | How many primes needed so product > 2^{n/2}?
primesNeeded :: Int -> Int
primesNeeded n =
  let target = 2.0 ** (fromIntegral n / 2.0) :: Double
      ps = firstKPrimes 200
      go [] _ _ = 200
      go (p:rest) prod k
        | prod > target = k
        | otherwise = go rest (prod * fromIntegral p) (k + 1)
  in go ps 1.0 0

-- | Modular signature: encode residues mod each prime as single Int
-- Using mixed-radix encoding
encodeModSig :: Int -> [Int] -> Int
encodeModSig s primes = foldl' (\acc p -> acc * p + (s `mod` p)) 0 primes

-- | Required RIGHT mod signature given LEFT mod sig and target
requiredRightModSig :: Int -> Int -> [Int] -> Int
requiredRightModSig leftModSig target primes =
  -- Decode left, compute required right for each prime, re-encode
  let decode enc [] = []
      decode enc (p:ps) = let (rest, r) = enc `divMod` p in r : decode rest ps
      leftResidues = decode leftModSig (reverse primes)
      targetResidues = [target `mod` p | p <- primes]
      rightResidues = zipWith (\t l -> (t - l) `mod` (primes !! idx))
                        targetResidues leftResidues
                        where idx = 0  -- dummy, fixed below
  in -- Actually, do it properly:
     let pairs = zip3 primes
                      [target `mod` p | p <- primes]
                      (decodeAll leftModSig primes)
         rightRes = [(tR - lR) `mod` p | (p, tR, lR) <- pairs]
     in foldl' (\acc (p, r) -> acc * p + r) 0 (zip primes rightRes)

decodeAll :: Int -> [Int] -> [Int]
decodeAll _ [] = []
decodeAll enc (p:ps) = let rest = decodeAll (enc `div` p) ps
                       in (enc `mod` p) : rest

-- | Enumerate half with mod signature only (lean version)
enumHalfModSig :: [Int] -> [Int] -> Map.Map Int [Int]
-- Returns: modSig → [sum values]
enumHalfModSig weights primes =
  let n = length weights
      go idx partial acc
        | idx >= n =
            let sig = encodeModSig partial primes
            in Map.insertWith (++) sig [partial] acc
        | otherwise =
            let w = weights !! idx
                acc1 = go (idx+1) partial acc
                acc2 = go (idx+1) (partial + w) acc1
            in acc2
  in go 0 0 Map.empty

-- | HASH-BASED catalog MITM: O(left_sigs) matching, not O(left×right)
hashCatalogMITM :: [Int] -> Int -> [Int]
               -> (Bool, Int, Int, Int, Int)
-- Returns: (found, leftSigs, rightSigs, hashHits, totalLookups)
hashCatalogMITM weights target primes =
  let n = length weights
      mid = n `div` 2
      leftW = take mid weights
      rightW = drop mid weights
      leftCat = enumHalfModSig leftW primes
      rightCat = enumHalfModSig rightW primes
      leftSumSet = IS.fromList (concat (Map.elems leftCat))
      -- For each RIGHT sig, compute REQUIRED left sig and lookup
      rightEntries = Map.toList rightCat
      (found, hits, lookups) = foldl' (\(f, h, l) (rSig, rSums) ->
        let reqLeftSig = requiredRightModSig rSig target primes
            -- but we need it the other way: for this right sig,
            -- what left sig is needed?
            -- Actually: required left = encode of ((T - rSum) mod p for each p)
            -- But rSum varies within the sig bucket!
            -- The modular constraint is: leftMod + rightMod ≡ targetMod (per prime)
            -- So requiredLeftMod is fixed for a given rightMod (independent of sum)
            reqLeft = requiredLeftSig rSig target primes
        in case Map.lookup reqLeft leftCat of
             Nothing -> (f, h, l + 1)  -- no compatible left sig
             Just leftSums ->
               let matched = any (\rS -> IS.member (target - rS) leftSumSet) rSums
               in (f || matched, h + 1, l + 1 + length rSums)
        ) (False, 0, 0) rightEntries
  in (found, Map.size leftCat, Map.size rightCat, hits, lookups)

-- | Required LEFT mod sig given RIGHT mod sig and target
requiredLeftSig :: Int -> Int -> [Int] -> Int
requiredLeftSig rightModSig target primes =
  let rightRes = decodeAll rightModSig primes
      targetRes = [target `mod` p | p <- primes]
      leftRes = zipWith3 (\p tR rR -> (tR - rR) `mod` p) primes targetRes rightRes
  in foldl' (\acc (p, r) -> acc * p + r) 0 (zip primes leftRes)

-- | Plain MITM for comparison
plainMITM :: [Int] -> Int -> (Bool, Int)
plainMITM weights target =
  let mid = length weights `div` 2
      leftSums = foldl' (\acc w -> IS.union acc (IS.map (+w) acc)) (IS.singleton 0) (take mid weights)
      rightSums = foldl' (\acc w -> IS.union acc (IS.map (+w) acc)) (IS.singleton 0) (drop mid weights)
      found = IS.foldl' (\f r -> f || IS.member (target - r) leftSums) False rightSums
  in (found, IS.size leftSums + IS.size rightSums)

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
  putStrLn " DYNAMIC RICH CATALOG: adaptive primes + O(1) hash matching"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: How many primes needed per n?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. DYNAMIC PRIMES: how many to cover 2^{n/2}? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "2^(n/2)" ++ padR 10 "#primes"
    ++ padR 12 "max_prime" ++ padR 14 "product" ++ padR 12 "oracle_cost"
  putStrLn (replicate 64 '-')
  mapM_ (\n -> do
    let k = primesNeeded n
        ps = firstKPrimes k
        maxP = if null ps then 0 else last ps
        prod = product (map toInteger ps)
        oracleCost = n * sum ps  -- O(n × Σp)
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show ((2::Int)^(n `div` 2)))
      ++ padR 10 (show k)
      ++ padR 12 (show maxP)
      ++ padR 14 (show prod)
      ++ padR 12 (show oracleCost)
    ) [8, 12, 16, 20, 24, 28, 32, 40, 50, 60]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Hash-based matching with dynamic primes
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. HASH MATCHING: dynamic primes + O(sigs) match ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 8 "#p" ++ padR 10 "sigs"
    ++ padR 10 "hits" ++ padR 10 "lookups" ++ padR 10 "plain"
    ++ padR 10 "speedup"
  putStrLn (replicate 70 '-')
  mapM_ (\n -> do
    let k = primesNeeded n
        ps = firstKPrimes k
    -- YES
    let (wsY, tY) = mkHashYes n
        (fY, lSigY, rSigY, hitsY, lookupsY) = hashCatalogMITM wsY tY ps
        (pfY, plainY) = plainMITM wsY tY
        spY = fromIntegral plainY / fromIntegral (max 1 lookupsY) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES" ++ padR 8 (show k)
      ++ padR 10 (show lSigY) ++ padR 10 (show hitsY)
      ++ padR 10 (show lookupsY) ++ padR 10 (show plainY)
      ++ padR 10 (showF 1 spY ++ "x")
    -- NO
    let (wsN, tN) = mkHash n
        (fN, lSigN, rSigN, hitsN, lookupsN) = hashCatalogMITM wsN tN ps
        (pfN, plainN) = plainMITM wsN tN
        spN = fromIntegral plainN / fromIntegral (max 1 lookupsN) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO" ++ padR 8 (show k)
      ++ padR 10 (show lSigN) ++ padR 10 (show hitsN)
      ++ padR 10 (show lookupsN) ++ padR 10 (show plainN)
      ++ padR 10 (showF 1 spN ++ "x")
    ) [8, 12, 16, 20, 24, 28]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Correctness verification
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. CORRECTNESS: dynamic catalog vs plain MITM ==="
  putStrLn ""
  mapM_ (\n -> do
    let k = primesNeeded n
        ps = firstKPrimes k
        (wsY, tY) = mkHashYes n
        (fY, _, _, _, _) = hashCatalogMITM wsY tY ps
        (pfY, _) = plainMITM wsY tY
        (wsN, tN) = mkHash n
        (fN, _, _, _, _) = hashCatalogMITM wsN tN ps
        (pfN, _) = plainMITM wsN tN
    putStrLn $ "  n=" ++ show n ++ " primes=" ++ show k
      ++ " YES:" ++ show fY ++ "=" ++ show pfY
      ++ " NO:" ++ show fN ++ "=" ++ show pfN
      ++ (if fY == pfY && fN == pfN then " ✓" else " ✗ MISMATCH!")
    ) [8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: Total cost breakdown
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. TOTAL COST: oracle + enum + match ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "oracle" ++ padR 10 "enum"
    ++ padR 10 "match" ++ padR 12 "total" ++ padR 10 "plain"
    ++ padR 10 "ratio"
  putStrLn (replicate 68 '-')
  mapM_ (\n -> do
    let k = primesNeeded n
        ps = firstKPrimes k
        oracleCost = n * sum ps
        enumCost = 2 * (2::Int)^(n `div` 2)  -- both halves
        (ws, t) = mkHash n
        (_, _, rSigs, _, matchCost) = hashCatalogMITM ws t ps
        totalCost = oracleCost + enumCost + matchCost
        (_, plainCost) = plainMITM ws t
        ratio = fromIntegral totalCost / fromIntegral (max 1 plainCost) :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show oracleCost)
      ++ padR 10 (show enumCost)
      ++ padR 10 (show matchCost)
      ++ padR 12 (show totalCost)
      ++ padR 10 (show plainCost)
      ++ padR 10 (showF 2 ratio)
    ) [8, 12, 16, 20, 24, 28]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "KEY INSIGHT:"
  putStrLn " With O(n/log n) primes, the modular filter NEVER saturates."
  putStrLn " Hash matching is O(right_sigs) not O(left × right)."
  putStrLn ""
  putStrLn " Total cost = O(2^{n/2}) [enum] + O(n³ log n) [oracle]"
  putStrLn "            + O(2^{n/2}/∏pᵢ × 2^{n/2}) [match]"
  putStrLn ""
  putStrLn " If ∏pᵢ > 2^{n/2}: match cost = O(2^{n/2}) × (1/∏pᵢ × 2^{n/2})"
  putStrLn "                   = O(2^n / ∏pᵢ) = O(1) when ∏pᵢ > 2^{n/2}!"
  putStrLn ""
  putStrLn " But the ENUMERATION of 2^{n/2} sums still dominates."
  putStrLn " The catalog optimizes MATCHING, not ENUMERATION."
  putStrLn " To go truly polynomial: need to avoid enumerating all sums."
  putStrLn "═══════════════════════════════════════════════════════════════════"
