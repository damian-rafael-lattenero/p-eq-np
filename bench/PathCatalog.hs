module Main where

-- PATH CATALOG: catalog midpoint sums by STRUCTURAL properties of the
-- path that generated them, not just the sum value.
--
-- Standard MITM: catalog by VALUE → hash(sum) → O(1) lookup
-- Path catalog: catalog by STRUCTURE → (cardinality, parity_pattern,
--   bit_signature, weight_class_distribution) → multi-key index
--
-- The question: do structural properties of the LEFT path constrain
-- which RIGHT paths can complete the solution?
--
-- If yes: we can prune right-half enumeration based on left-path structure
-- without ever computing the right half exhaustively.
--
-- Properties tracked per path:
--   1. Cardinality (how many weights included)
--   2. Parity signature (how many odd/even weights)
--   3. Bit signature (which bits are "hot" in the partial sum)
--   4. Weight-class: light/medium/heavy items used
--   5. Modular fingerprint (sum mod p for several primes)

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import Data.List (foldl', sort, group, sortBy)
import Data.Ord (comparing, Down(..))
import Data.Bits (xor, shiftR, (.&.), shiftL, popCount)
import PeqNP.ActorSolver (padR)

-- | Path signature: structural fingerprint of the subset that produced a sum
data PathSig = PathSig
  { psCard      :: !Int    -- number of weights used
  , psOddCount  :: !Int    -- number of odd weights used
  , psBitPop    :: !Int    -- popcount of the partial sum (how many bits set)
  , psHeavy     :: !Int    -- number of "heavy" weights (above median)
  , psModSig    :: !Int    -- combined modular signature: (sum mod 3)*100 + (sum mod 7)*10 + (sum mod 11)
  } deriving (Show, Eq, Ord)

-- | Compute path signature for a partial sum and its generating subset
mkPathSig :: Int -> Int -> Int -> [Bool] -> [Int] -> PathSig
mkPathSig partialSum card oddCount choices weights =
  let heavy = length [() | (True, w) <- zip choices weights, w > median]
      median = sort weights !! (length weights `div` 2)
      modSig = (partialSum `mod` 3) * 100 + (partialSum `mod` 7) * 10 + (partialSum `mod` 11)
  in PathSig card oddCount (popCount partialSum) heavy modSig

-- | Enumerate all left-half subsets with their path signatures
-- Returns: Map PathSig [(sum, bitmask)]
catalogLeftHalf :: [Int] -> Map.Map PathSig [(Int, Int)]
catalogLeftHalf weights =
  let n = length weights
      median = sort weights !! (n `div` 2)
      go :: Int -> Int -> Int -> Int -> Int -> Int -> Map.Map PathSig [(Int, Int)]
         -> Map.Map PathSig [(Int, Int)]
      go idx partial card oddCt heavyCt mask acc
        | idx >= n =
            let sig = PathSig card oddCt (popCount partial) heavyCt
                        ((partial `mod` 3) * 100 + (partial `mod` 7) * 10 + (partial `mod` 11))
            in Map.insertWith (++) sig [(partial, mask)] acc
        | otherwise =
            let w = weights !! idx
                -- Branch OUT
                acc1 = go (idx+1) partial card oddCt heavyCt mask acc
                -- Branch IN
                card' = card + 1
                oddCt' = if odd w then oddCt + 1 else oddCt
                heavyCt' = if w > median then heavyCt + 1 else heavyCt
                mask' = mask + shiftL 1 idx
                acc2 = go (idx+1) (partial + w) card' oddCt' heavyCt' mask' acc1
            in acc2
  in go 0 0 0 0 0 0 Map.empty

-- | For a target T and right-half weights, what path signature is REQUIRED
-- from the left half?
requiredSigRange :: Int -> Int -> [Int] -> [PathSig]
requiredSigRange target rightSum rightWeights =
  let leftNeeded = target - rightSum  -- this is what left sum must be... but varies
      -- Actually: for each right subset R, left must be T - sum(R)
      -- The required LEFT signature depends on T - rightSum specifics
      -- We can constrain:
      --   left_card + right_card ∈ [some range]
      --   left_odd + right_odd must make T's parity work
      --   left_modSig + right_modSig ≡ T's modSig
      -- This is a COMPATIBILITY constraint between signatures
  in []  -- computed dynamically below

-- | Check if two path signatures are COMPATIBLE for target T
-- Left sig + right sig could produce T?
sigCompatible :: PathSig -> PathSig -> Int -> Int -> Bool
sigCompatible left right target nTotal =
  let -- Cardinality: total items used must be ≤ n
      cardOk = psCard left + psCard right <= nTotal
      -- Parity: if T is odd, need odd number of odd-weight items total
      parityOk = let totalOdd = psOddCount left + psOddCount right
                 in even target == even totalOdd || odd target == odd totalOdd
                 -- Actually: sum parity = parity of (sum of included weights)
                 -- This is already captured by modSig
      -- Modular: combined mod signatures must match T
      mod3ok = ((psModSig left `div` 100) + (psModSig right `div` 100)) `mod` 3 == target `mod` 3
      mod7ok = (((psModSig left `mod` 100) `div` 10) + ((psModSig right `mod` 100) `div` 10)) `mod` 7 == target `mod` 7
      mod11ok = ((psModSig left `mod` 10) + (psModSig right `mod` 10)) `mod` 11 == target `mod` 11
  in cardOk && mod3ok && mod7ok && mod11ok

-- | CATALOG MITM: use path signatures to prune matching
catalogMITM :: [Int] -> Int -> (Bool, Int, Int, Int, Int, Int)
-- Returns: (found, left_sigs, right_sigs, compatible_pairs, actual_lookups, plain_mitm_lookups)
catalogMITM weights target =
  let n = length weights
      mid = n `div` 2
      leftW = take mid weights
      rightW = drop mid weights
      -- Build left catalog
      leftCat = catalogLeftHalf leftW
      leftSigCount = Map.size leftCat
      -- Build right catalog
      rightCat = catalogLeftHalf rightW
      rightSigCount = Map.size rightCat
      -- Build left sum lookup (for final matching)
      leftSumSet = IS.fromList [s | entries <- Map.elems leftCat, (s, _) <- entries]
      -- Count compatible signature pairs
      leftSigs = Map.keys leftCat
      rightSigs = Map.keys rightCat
      compatPairs = [(ls, rs) | ls <- leftSigs, rs <- rightSigs,
                                sigCompatible ls rs target n]
      numCompat = length compatPairs
      -- Actual matching: only check sums from compatible signature pairs
      matchResults = [IS.member (target - rSum) leftSumSet
                     | (ls, rs) <- compatPairs
                     , (rSum, _) <- Map.findWithDefault [] rs rightCat]
      actualLookups = length matchResults
      found = any id matchResults
      -- Plain MITM would check all right sums
      plainLookups = sum [length entries | entries <- Map.elems rightCat]
  in (found, leftSigCount, rightSigCount, numCompat, actualLookups, plainLookups)

-- | Standard MITM for comparison
plainMITM :: [Int] -> Int -> (Bool, Int)
plainMITM weights target =
  let n = length weights
      mid = n `div` 2
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
  putStrLn " PATH CATALOG: index midpoint sums by STRUCTURAL path properties"
  putStrLn " Not just WHAT the sum is, but HOW it was built"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: How many distinct signatures exist?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. SIGNATURE SPACE: how many distinct path signatures? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "2^(n/2)" ++ padR 10 "left-sig"
    ++ padR 10 "right-sig" ++ padR 12 "compression"
  putStrLn (replicate 48 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (_, lSig, rSig, _, _, _) = catalogMITM ws t
        halfN = (2::Int)^(n `div` 2)
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show halfN)
      ++ padR 10 (show lSig)
      ++ padR 10 (show rSig)
      ++ padR 12 (showF 1 (fromIntegral halfN / fromIntegral (max 1 lSig) :: Double) ++ "x")
    ) [8, 10, 12, 14, 16]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Compatible pairs — how many sig pairs survive?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. COMPATIBLE PAIRS: sig pairs that could produce T ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "all-pairs" ++ padR 10 "compat"
    ++ padR 10 "filter%" ++ padR 12 "lookups" ++ padR 10 "plain"
  putStrLn (replicate 52 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (_, lSig, rSig, compat, lookups, plain) = catalogMITM ws t
        allPairs = lSig * rSig
        filterPct = if allPairs == 0 then 0
                    else (1 - fromIntegral compat / fromIntegral allPairs) * 100 :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show allPairs)
      ++ padR 10 (show compat)
      ++ padR 10 (showF 1 filterPct ++ "%")
      ++ padR 12 (show lookups)
      ++ padR 10 (show plain)
    ) [8, 10, 12, 14, 16]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Signature distribution — are sums clustered?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. SIGNATURE CLUSTERS: sums per signature (n=12) ==="
  putStrLn "   (uniform = no structure, clustered = exploitable)"
  putStrLn ""
  let (ws3, t3) = mkHash 12
      leftCat3 = catalogLeftHalf (take 6 ws3)
      sizes = sort $ map length (Map.elems leftCat3)
      total3 = sum sizes
  putStrLn $ "  Total sums: " ++ show total3
    ++ ", Signatures: " ++ show (length sizes)
  putStrLn $ "  Sums per signature: min=" ++ show (head sizes)
    ++ " max=" ++ show (last sizes)
    ++ " mean=" ++ showF 1 (fromIntegral total3 / fromIntegral (length sizes) :: Double)
  putStrLn $ "  Distribution (top 10 by size): "
    ++ show (take 10 (reverse sizes))
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: Correctness + speedup
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. SPEEDUP: catalog MITM vs plain MITM ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 10 "plain"
    ++ padR 10 "catalog" ++ padR 10 "speedup" ++ padR 8 "correct"
  putStrLn (replicate 50 '-')
  mapM_ (\n -> do
    -- YES
    let (wsY, tY) = mkHashYes n
        (plainFoundY, plainWork) = plainMITM wsY tY
        (catFoundY, _, _, _, catLookups, _) = catalogMITM wsY tY
        speedupY = fromIntegral plainWork / fromIntegral (max 1 catLookups) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 10 (show plainWork)
      ++ padR 10 (show catLookups)
      ++ padR 10 (showF 1 speedupY ++ "x")
      ++ padR 8 (if catFoundY == plainFoundY then "OK" else "ERR")
    -- NO
    let (wsN, tN) = mkHash n
        (plainFoundN, plainWorkN) = plainMITM wsN tN
        (catFoundN, _, _, _, catLookupsN, _) = catalogMITM wsN tN
        speedupN = fromIntegral plainWorkN / fromIntegral (max 1 catLookupsN) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 10 (show plainWorkN)
      ++ padR 10 (show catLookupsN)
      ++ padR 10 (showF 1 speedupN ++ "x")
      ++ padR 8 (if catFoundN == plainFoundN then "OK" else "ERR")
    ) [8, 10, 12, 14, 16]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: Scaling — does signature compression grow?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. SCALING: signatures / 2^{n/2} ==="
  putStrLn "   sig/2^{n/2} → 0 : signatures compress exponentially → win!"
  putStrLn "   sig/2^{n/2} → 1 : each sum is its own signature → no help"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "sigs" ++ padR 10 "2^(n/2)"
    ++ padR 10 "ratio" ++ padR 10 "sigs/n²"
  putStrLn (replicate 46 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (_, lSig, _, _, _, _) = catalogMITM ws t
        halfN = (2::Int)^(n `div` 2)
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show lSig)
      ++ padR 10 (show halfN)
      ++ padR 10 (showF 4 (fromIntegral lSig / fromIntegral halfN :: Double))
      ++ padR 10 (showF 2 (fromIntegral lSig / fromIntegral (n*n) :: Double))
    ) [8, 10, 12, 14, 16, 18]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "ANALYSIS:"
  putStrLn " Path signatures compress 2^{n/2} sums into fewer categories."
  putStrLn " Compatible pairs filter out impossible left-right combinations."
  putStrLn ""
  putStrLn " If signatures << 2^{n/2} AND compatible pairs << all pairs:"
  putStrLn "   → The PATH structure carries info that VALUES don't"
  putStrLn "   → Catalog MITM beats plain MITM by reducing matching"
  putStrLn ""
  putStrLn " The key insight: it's not just WHERE you are (the sum value)"
  putStrLn " but HOW you got there (which weights, which pattern)."
  putStrLn "═══════════════════════════════════════════════════════════════════"
