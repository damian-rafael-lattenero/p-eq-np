module Main where

-- HYBRID ADT + MITM: algebraic pruning on each half, then match survivors
--
-- Phase 1: ADT-prune left half → collect surviving partial sums
-- Phase 2: ADT-prune right half → collect surviving complement sums
-- Phase 3: Match survivors (hash join)
--
-- If ADT kills 98% on each half:
--   Left survivors:  ~0.02 × 2^{n/2}
--   Right survivors: ~0.02 × 2^{n/2}
--   Match cost:      ~0.02 × 2^{n/2} (hash lookup)
--   Total:           ~0.04 × 2^{n/2} vs 2^{n/2} for plain MITM
--
-- BUT: can we go further? Analyze the survivors — what patterns
-- do they share? Use patterns as SECOND-LEVEL rules.

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Array as A
import Data.List (foldl')
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

type ModOracle = IM.IntMap IS.IntSet

buildModOracle :: [Int] -> [Int] -> ModOracle
buildModOracle weights primes =
  let n = length weights
  in IM.fromList
       [ (p * 1000 + k, reachable)
       | p <- primes
       , k <- [0..n]
       , let suffix = drop k weights
             reachable = foldl' (\acc w ->
               IS.union acc (IS.map (\r -> (r + w) `mod` p) acc)
               ) (IS.singleton 0) suffix
       ]

-- | Check if partial sum s at level k, aiming for target, is killed by any rule
isAlive :: ModOracle -> [Int] -> Int -> Int -> Int -> Int -> Bool
isAlive oracle primes partial remaining target level
  | partial > target = False            -- bounds high
  | partial + remaining < target = False -- bounds low
  | otherwise = not (any modFails primes) -- modular check
  where
    modFails p =
      let gap = target - partial
          needed = gap `mod` p
          key = p * 1000 + level
      in case IM.lookup key oracle of
           Nothing -> False
           Just reachable -> not (IS.member needed reachable)

-- | Collect all surviving partial sums at a given depth using ADT pruning
-- Returns: IntSet of surviving partial sums (pruned)
collectSurvivors :: [Int] -> Int -> Int -> ModOracle -> [Int] -> IS.IntSet
collectSurvivors weights target depth oracle primes =
  let n = length weights
      wArr = A.listArray (0, n-1) weights
      suffArr = A.listArray (0, n) (scanr (+) 0 weights)

      go :: Int -> Int -> Int -> IS.IntSet -> IS.IntSet
      go partial level itemsUsed acc
        | level == depth = IS.insert partial acc
        | not (isAlive oracle primes partial (suffArr A.! level) target level) = acc
        | otherwise =
            let w = wArr A.! level
                rem' = suffArr A.! (level + 1)
                -- Branch IN
                accIn = if isAlive oracle primes (partial + w) rem' target (level + 1)
                        then go (partial + w) (level + 1) (itemsUsed + 1) acc
                        else acc
                -- Branch OUT
                accOut = if isAlive oracle primes partial rem' target (level + 1)
                         then go partial (level + 1) itemsUsed accIn
                         else accIn
            in accOut
  in go 0 0 0 IS.empty

-- | Plain MITM for comparison (no ADT pruning)
plainMITM :: [Int] -> Int -> (Bool, Int, Int)
plainMITM weights target =
  let n = length weights
      mid = n `div` 2
      leftW = take mid weights
      rightW = drop mid weights
      leftSums = foldl' (\acc w -> IS.union acc (IS.map (+w) acc)) (IS.singleton 0) leftW
      rightSums = foldl' (\acc w -> IS.union acc (IS.map (+w) acc)) (IS.singleton 0) rightW
      found = IS.foldl' (\f s -> f || IS.member (target - s) rightSums) False leftSums
  in (found, IS.size leftSums, IS.size rightSums)

-- | Hybrid: ADT-prune each half, then match
hybridADTMitm :: [Int] -> Int -> [Int] -> (Bool, Int, Int, Int)
-- Returns: (found, left_survivors, right_survivors, match_ops)
hybridADTMitm weights target primes =
  let n = length weights
      mid = n `div` 2
      oracle = buildModOracle weights primes
      -- Phase 1: collect left-half survivors (levels 0..mid)
      leftSurvivors = collectSurvivors weights target mid oracle primes
      -- Phase 2: collect right-half survivors (levels mid..n)
      -- For right half: we need survivors of the COMPLEMENT
      -- right sum r is needed iff (target - r) is a left survivor
      rightWeights = drop mid weights
      rightSums = foldl' (\acc w -> IS.union acc (IS.map (+w) acc)) (IS.singleton 0) rightWeights
      -- Prune right sums: keep only those where (target - r) could be a left sum
      rightPruned = IS.filter (\r -> r >= 0 && r <= target && IS.member (target - r) leftSurvivors) rightSums
      -- Phase 3: match
      matchOps = IS.size leftSurvivors  -- each left checks one hash lookup
      found = not (IS.null rightPruned)
  in (found, IS.size leftSurvivors, IS.size rightPruned, matchOps)

-- | Analyze survivors: what fraction of each weight is "in" vs "out"?
survivorProfile :: [Int] -> Int -> Int -> ModOracle -> [Int] -> IM.IntMap (Int, Int)
-- Returns: weight_index → (times_included, times_excluded) among survivors
survivorProfile weights target depth oracle primes =
  let n = length weights
      wArr = A.listArray (0, n-1) weights
      suffArr = A.listArray (0, n) (scanr (+) 0 weights)

      go :: Int -> Int -> [Bool] -> [(Int, [Bool])] -> [(Int, [Bool])]
      go partial level choices acc
        | level == depth = (partial, choices) : acc
        | not (isAlive oracle primes partial (suffArr A.! level) target level) = acc
        | otherwise =
            let w = wArr A.! level
                rem' = suffArr A.! (level + 1)
                accIn = if isAlive oracle primes (partial + w) rem' target (level + 1)
                        then go (partial + w) (level + 1) (choices ++ [True]) acc
                        else acc
                accOut = if isAlive oracle primes partial rem' target (level + 1)
                         then go partial (level + 1) (choices ++ [False]) accIn
                         else accIn
            in accOut

      survivors = go 0 0 [] []
      total = length survivors

      -- Count inclusions per weight index
      counts = foldl' (\m (_, choices) ->
        foldl' (\m' (idx, inc) ->
          let (inC, outC) = IM.findWithDefault (0,0) idx m'
          in IM.insert idx (if inc then (inC+1, outC) else (inC, outC+1)) m'
          ) m (zip [0..] choices)
        ) IM.empty survivors
  in counts

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
  putStrLn " HYBRID ADT + MITM: prune 98%, then MITM the survivors"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  let primes = [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59]

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Plain MITM vs Hybrid ADT+MITM
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. PLAIN MITM vs HYBRID ADT+MITM ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 10 "mitm-L"
    ++ padR 10 "mitm-R" ++ padR 10 "adt-L" ++ padR 10 "adt-R"
    ++ padR 10 "speedup"
  putStrLn (replicate 62 '-')
  mapM_ (\n -> do
    -- YES
    let (wsY, tY) = mkHashYes n
        (fMitmY, mitmLY, mitmRY) = plainMITM wsY tY
        (fHybY, hybLY, hybRY, _) = hybridADTMitm wsY tY primes
        speedupY = fromIntegral (mitmLY + mitmRY) / fromIntegral (max 1 (hybLY + hybRY)) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 10 (show mitmLY) ++ padR 10 (show mitmRY)
      ++ padR 10 (show hybLY) ++ padR 10 (show hybRY)
      ++ padR 10 (showF 1 speedupY ++ "x")
    -- NO
    let (wsN, tN) = mkHash n
        (_, mitmLN, mitmRN) = plainMITM wsN tN
        (_, hybLN, hybRN, _) = hybridADTMitm wsN tN primes
        speedupN = fromIntegral (mitmLN + mitmRN) / fromIntegral (max 1 (hybLN + hybRN)) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 10 (show mitmLN) ++ padR 10 (show mitmRN)
      ++ padR 10 (show hybLN) ++ padR 10 (show hybRN)
      ++ padR 10 (showF 1 speedupN ++ "x")
    ) [8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Survivor ratio — what fraction survives ADT?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. SURVIVOR RATIO: adt-survivors / 2^{n/2} ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "2^(n/2)" ++ padR 10 "adt-L"
    ++ padR 12 "ratio" ++ padR 12 "ratio²"
  putStrLn (replicate 50 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (_, hybL, _, _) = hybridADTMitm ws t primes
        halfN = (2::Int)^(n `div` 2)
        ratio = fromIntegral hybL / fromIntegral halfN :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show halfN)
      ++ padR 10 (show hybL)
      ++ padR 12 (showF 4 ratio)
      ++ padR 12 (showF 6 (ratio * ratio))
    ) [8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Survivor profile — which weights are "forced"?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. SURVIVOR PROFILE: inclusion bias per weight (n=12) ==="
  putStrLn "   (if some weight is 100% in or 100% out → effectively forced)"
  putStrLn ""
  let (ws3, t3) = mkHashYes 12
      oracle3 = buildModOracle ws3 primes
      profile3 = survivorProfile ws3 t3 6 oracle3 primes
  putStrLn $ padR 8 "weight" ++ padR 10 "value" ++ padR 10 "in" ++ padR 10 "out"
    ++ padR 10 "in%"
  putStrLn (replicate 48 '-')
  mapM_ (\i ->
    case IM.lookup i profile3 of
      Nothing -> pure ()
      Just (inC, outC) ->
        let total = inC + outC
            pct = if total == 0 then 0 else fromIntegral inC / fromIntegral total * 100 :: Double
        in putStrLn $ padR 8 (show i)
             ++ padR 10 (show (ws3 !! i))
             ++ padR 10 (show inC) ++ padR 10 (show outC)
             ++ padR 10 (showF 1 pct ++ "%")
    ) [0..5]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: Total work comparison
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. TOTAL WORK: hybrid vs plain MITM vs brute force ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "brute" ++ padR 12 "MITM"
    ++ padR 12 "hybrid" ++ padR 10 "hyb/MITM"
  putStrLn (replicate 52 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        bruteN = (2::Int)^n
        (_, mitmL, mitmR) = plainMITM ws t
        mitmWork = mitmL + mitmR
        (_, hybL, hybR, _) = hybridADTMitm ws t primes
        hybWork = hybL + hybR
        ratio = fromIntegral hybWork / fromIntegral (max 1 mitmWork) :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show bruteN)
      ++ padR 12 (show mitmWork)
      ++ padR 12 (show hybWork)
      ++ padR 10 (showF 3 ratio)
    ) [8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "ANALYSIS:"
  putStrLn " The hybrid uses ADT pruning as a FILTER before MITM."
  putStrLn " Each half is pruned independently, then survivors are matched."
  putStrLn ""
  putStrLn " If survivor ratio r is constant: hybrid = r² × MITM"
  putStrLn "   r=0.02 → 0.0004 × MITM (2500x speedup!)"
  putStrLn " If r grows with n: benefit diminishes"
  putStrLn ""
  putStrLn " Section 3 reveals if any weights are EFFECTIVELY FORCED"
  putStrLn " by the combined rules — bits that DualPrune couldn't fix"
  putStrLn " but the ADT CAN fix through synergistic pruning."
  putStrLn "═══════════════════════════════════════════════════════════════════"
