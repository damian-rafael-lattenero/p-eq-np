module Main where

-- RICH CATALOG: expanded path signature with NONLINEAR dimensions
--
-- Previous PathCatalog used: (card, oddCount, bitPop, heavy, mod 3×7×11)
-- → 0% compression, 99.6% pair filtering, but dilutes at large n
--
-- This version adds NONLINEAR properties:
--   sum_of_squares:  Σ wᵢ² (independent from Σ wᵢ)
--   xor_signature:   XOR of included weights (captures bit-level structure)
--   max_weight:      largest included weight
--   mod_expanded:    more primes (3,5,7,11,13,17,19,23)
--
-- KEY QUESTION: do nonlinear properties break the uniform distribution
-- that kills modular approaches at density-1?

import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import Data.List (foldl', sort)
import Data.Bits (xor, shiftR, (.&.), popCount)
import PeqNP.ActorSolver (padR)

-- | Rich path signature
data RichSig = RichSig
  { rsCard    :: !Int  -- cardinality
  , rsSumSq   :: !Int  -- sum of squares (bucketed)
  , rsXor     :: !Int  -- XOR of included weights (bucketed)
  , rsMaxW    :: !Int  -- max included weight (bucketed)
  , rsMod     :: !Int  -- multi-prime mod: encoded as single int
  } deriving (Show, Eq, Ord)

-- | Primes for modular signature
modPrimes :: [Int]
modPrimes = [3, 5, 7, 11, 13, 17, 19, 23]

-- | Encode modular residues as single integer
encodeMod :: Int -> Int
encodeMod s = foldl' (\acc p -> acc * p + (s `mod` p)) 0 modPrimes

-- | Bucket a value into B buckets over range [0, maxVal]
bucket :: Int -> Int -> Int -> Int
bucket val maxVal numBuckets =
  if maxVal <= 0 then 0
  else min (numBuckets - 1) (val * numBuckets `div` max 1 (maxVal + 1))

-- | Enumerate left half with rich signatures
-- Returns: Map RichSig [sum]  and  Map sum RichSig
enumWithSig :: [Int] -> Int -> Int -> (Map.Map RichSig [Int], Int)
-- weights, sqBuckets, xorBuckets → (catalog, total_sums)
enumWithSig weights sqBuckets xorBuckets =
  let n = length weights
      totalSq = sum [w*w | w <- weights]
      maxXor = foldl' Data.Bits.xor 0 weights
      maxW = if null weights then 0 else maximum weights

      go :: Int -> Int -> Int -> Int -> Int -> Int -> Map.Map RichSig [Int]
         -> Map.Map RichSig [Int]
      go idx partial card sumSq xorAcc maxIncl acc
        | idx >= n =
            let sig = RichSig
                  { rsCard = card
                  , rsSumSq = bucket sumSq totalSq sqBuckets
                  , rsXor = bucket xorAcc (maxXor + 1) xorBuckets
                  , rsMaxW = bucket maxIncl maxW sqBuckets
                  , rsMod = encodeMod partial
                  }
            in Map.insertWith (++) sig [partial] acc
        | otherwise =
            let w = weights !! idx
                -- OUT
                acc1 = go (idx+1) partial card sumSq xorAcc maxIncl acc
                -- IN
                acc2 = go (idx+1) (partial+w) (card+1) (sumSq+w*w)
                          (Data.Bits.xor xorAcc w) (max maxIncl w) acc1
            in acc2

      catalog = go 0 0 0 0 0 0 Map.empty
      totalSums = sum [length vs | vs <- Map.elems catalog]
  in (catalog, totalSums)

-- | Check compatibility of two rich signatures for target T
richCompatible :: RichSig -> RichSig -> Int -> Int -> Bool
richCompatible left right target nTotal =
  let -- Cardinality must be feasible
      cardOk = rsCard left + rsCard right <= nTotal
      -- Modular: decode and check each prime
      modOk = checkMods (rsMod left) (rsMod right) target (reverse modPrimes)
  in cardOk && modOk

checkMods :: Int -> Int -> Int -> [Int] -> Bool
checkMods _ _ _ [] = True
checkMods lEnc rEnc target (p:ps) =
  let lR = lEnc `mod` p
      rR = rEnc `mod` p
      tR = target `mod` p
      ok = (lR + rR) `mod` p == tR
  in ok && checkMods (lEnc `div` p) (rEnc `div` p) target ps

-- | Run the rich catalog MITM
richCatalogMITM :: [Int] -> Int -> Int -> Int
               -> (Bool, Int, Int, Int, Int, Int)
-- Returns: (found, leftSigs, rightSigs, compatPairs, catalogLookups, plainLookups)
richCatalogMITM weights target sqB xorB =
  let n = length weights
      mid = n `div` 2
      leftW = take mid weights
      rightW = drop mid weights
      (leftCat, leftTotal) = enumWithSig leftW sqB xorB
      (rightCat, rightTotal) = enumWithSig rightW sqB xorB
      leftSumSet = IS.fromList (concat (Map.elems leftCat))

      leftSigs = Map.keys leftCat
      rightSigs = Map.keys rightCat
      compatPairs = [(ls, rs) | ls <- leftSigs, rs <- rightSigs,
                                richCompatible ls rs target n]
      -- Match only compatible pairs
      results = [IS.member (target - rSum) leftSumSet
                | (_, rs) <- compatPairs
                , rSum <- Map.findWithDefault [] rs rightCat]
      lookups = length results
      found = any id results
  in (found, Map.size leftCat, Map.size rightCat, length compatPairs, lookups, rightTotal)

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
  putStrLn " RICH CATALOG: nonlinear dimensions in path signature"
  putStrLn " sum_of_squares + XOR + max_weight + 8 primes"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Signature compression with nonlinear dimensions
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. COMPRESSION: how many signatures vs 2^{n/2}? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "2^(n/2)" ++ padR 10 "sigs"
    ++ padR 10 "ratio" ++ padR 10 "compress"
  putStrLn (replicate 46 '-')
  mapM_ (\n -> do
    let (ws, _) = mkHash n
        mid = n `div` 2
        (cat, total) = enumWithSig (take mid ws) 8 8
        halfN = (2::Int)^mid
        sigs = Map.size cat
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show halfN)
      ++ padR 10 (show sigs)
      ++ padR 10 (showF 3 (fromIntegral sigs / fromIntegral halfN :: Double))
      ++ padR 10 (showF 1 (fromIntegral halfN / fromIntegral (max 1 sigs) :: Double) ++ "x")
    ) [8, 12, 16, 20, 24, 28]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Compatible pairs — the FILTERING power
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. FILTERING: compatible pairs / all pairs ==="
  putStrLn "   (8 primes product = 223,092,870 ≈ 2^27.7)"
  putStrLn "   (filter should break when 2^{n/2} > 2^27.7, i.e., n > 55)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "all-pair" ++ padR 10 "compat"
    ++ padR 10 "filter%" ++ padR 10 "lookups" ++ padR 10 "plain"
    ++ padR 10 "speedup"
  putStrLn (replicate 68 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (found, lSig, rSig, compat, lookups, plain) = richCatalogMITM ws t 8 8
        allPairs = lSig * rSig
        filterPct = if allPairs == 0 then 0
                    else (1 - fromIntegral compat / fromIntegral allPairs) * 100 :: Double
        speedup = fromIntegral plain / fromIntegral (max 1 lookups) :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show allPairs)
      ++ padR 10 (show compat)
      ++ padR 10 (showF 2 filterPct ++ "%")
      ++ padR 10 (show lookups)
      ++ padR 10 (show plain)
      ++ padR 10 (showF 1 speedup ++ "x")
    ) [8, 12, 16, 20, 24, 28]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Impact of each dimension (ablation)
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. ABLATION: which dimensions matter most? (n=14) ==="
  putStrLn ""
  let (ws3, t3) = mkHash 14
  -- Vary sqBuckets and xorBuckets
  putStrLn $ padR 8 "sqB" ++ padR 8 "xorB" ++ padR 10 "sigs"
    ++ padR 10 "compat" ++ padR 10 "lookups" ++ padR 10 "speedup"
  putStrLn (replicate 56 '-')
  mapM_ (\(sqB, xorB) -> do
    let (_, lSig, rSig, compat, lookups, plain) = richCatalogMITM ws3 t3 sqB xorB
        speedup = fromIntegral plain / fromIntegral (max 1 lookups) :: Double
    putStrLn $ padR 8 (show sqB) ++ padR 8 (show xorB)
      ++ padR 10 (show lSig) ++ padR 10 (show compat)
      ++ padR 10 (show lookups)
      ++ padR 10 (showF 1 speedup ++ "x")
    ) [(1,1), (4,1), (1,4), (4,4), (8,8), (16,16), (32,32)]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: Correctness across instances
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. CORRECTNESS: rich catalog vs plain MITM ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 10 "plain" ++ padR 10 "catalog"
    ++ padR 10 "speedup" ++ padR 8 "correct"
  putStrLn (replicate 50 '-')
  mapM_ (\n -> do
    -- YES
    let (wsY, tY) = mkHashYes n
        (plainFY, plainW) = plainMITM wsY tY
        (catFY, _, _, _, catL, _) = richCatalogMITM wsY tY 8 8
        spY = fromIntegral plainW / fromIntegral (max 1 catL) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 10 (show plainW) ++ padR 10 (show catL)
      ++ padR 10 (showF 1 spY ++ "x")
      ++ padR 8 (if catFY == plainFY then "OK" else "ERR")
    -- NO
    let (wsN, tN) = mkHash n
        (plainFN, plainWN) = plainMITM wsN tN
        (catFN, _, _, _, catLN, _) = richCatalogMITM wsN tN 8 8
        spN = fromIntegral plainWN / fromIntegral (max 1 catLN) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 10 (show plainWN) ++ padR 10 (show catLN)
      ++ padR 10 (showF 1 spN ++ "x")
      ++ padR 8 (if catFN == plainFN then "OK" else "ERR")
    ) [8, 12, 16, 20, 24, 28]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: THE KEY — lookups/2^{n/2} scaling to large n
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. SCALING: catalog lookups / 2^{n/2} (extended) ==="
  putStrLn "   2^{n/2} crosses prime product (2^27.7) around n=55"
  putStrLn "   If ratio stays 0: rich catalog is SUBLINEAR in MITM!"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "2^(n/2)" ++ padR 12 "lookups"
    ++ padR 10 "ratio" ++ padR 10 "look/n²"
  putStrLn (replicate 48 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (_, _, _, _, lookups, _) = richCatalogMITM ws t 8 8
        halfN = (2::Int)^(n `div` 2)
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show halfN)
      ++ padR 12 (show lookups)
      ++ padR 10 (showF 4 (fromIntegral lookups / fromIntegral halfN :: Double))
      ++ padR 10 (showF 2 (fromIntegral lookups / fromIntegral (n*n) :: Double))
    ) [8, 12, 16, 20, 24, 28]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "ANALYSIS:"
  putStrLn " Rich signatures add sum_of_squares, XOR, max_weight to the"
  putStrLn " modular fingerprint. These are NONLINEAR in the weights."
  putStrLn ""
  putStrLn " If nonlinear dimensions break the uniform distribution of"
  putStrLn " density-1 sums: the filter stays powerful as n grows."
  putStrLn " If not: same saturation as before, just with more buckets."
  putStrLn ""
  putStrLn " The dream: a dimension where density-1 sums CLUSTER"
  putStrLn " instead of spreading uniformly. THAT would be the crack."
  putStrLn "═══════════════════════════════════════════════════════════════════"
