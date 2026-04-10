module Main where

{-
  TREE FUSION: can we collapse the 2^n recursion tree?

  The DP recurrence for [x^T]∏(1+αᵢx^{wᵢ}) creates a binary tree:

    coeff(n, T) = coeff(n-1, T) + αₙ · coeff(n-1, T-wₙ)

  Full tree: 2^n leaves. With memoization on (level, value): O(n×T) nodes.

  KEY IDEA: what if many (level, value) pairs produce the SAME subtree?
  If coeff(k, s₁) and coeff(k, s₂) always give the same result, we can
  FUSE them into one node. The question: how many equivalence classes?

  Two states (k, s₁) and (k, s₂) are "fusable" if:
    For ALL remaining weight subsets S ⊆ {wₖ₊₁,...,wₙ}:
      s₁ + Σ_{i∈S} wᵢ = T  ⟺  s₂ + Σ_{i∈S} wᵢ = T

  i.e., they have the same YES/NO answer for the same remaining subsets.
  This means: s₁ and s₂ differ by an amount that's NOT achievable by
  the remaining weights. If (s₂ - s₁) is NOT a subset sum of remaining
  weights... that's circular!

  ALTERNATIVE FUSION: fuse by MODULAR EQUIVALENCE.
  If s₁ ≡ s₂ (mod M) for some M, and the answer only depends on
  s mod M (for remaining weights), then states are fusable.

  This experiment:
    1. DEMAND TREE: top-down recursion, count unique (level, value) demanded
    2. MODULAR FUSION: group states by s mod M, measure information loss
    3. COLLISION SEARCH: find weight-specific M where fusion preserves answers
    4. FUSION RATIO: unique_states / 2^n as a function of n
-}

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.IntSet as IS
import Data.List (foldl')
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- | Top-down demand-driven coefficient extraction
-- Returns: (coefficient_at_T, set_of_demanded_(level,value)_pairs)
demandCoeff :: [Int] -> Int -> (Int, Set.Set (Int, Int))
demandCoeff weights target =
  let n = length weights
      -- Memoization cache
      go :: Map.Map (Int, Int) Int -> Int -> Int -> Set.Set (Int, Int)
         -> (Int, Map.Map (Int, Int) Int, Set.Set (Int, Int))
      go cache k s demanded
        | s < 0     = (0, cache, demanded)
        | s == 0 && k == 0 = (1, cache, Set.insert (0, 0) demanded)
        | k == 0    = (0, cache, Set.insert (0, s) demanded)
        | otherwise = case Map.lookup (k, s) cache of
            Just v  -> (v, cache, demanded)
            Nothing ->
              let demanded' = Set.insert (k, s) demanded
                  w = weights !! (k - 1)
                  -- coeff(k, s) = coeff(k-1, s) + coeff(k-1, s-w)
                  (v1, cache1, dem1) = go cache  (k-1) s     demanded'
                  (v2, cache2, dem2) = go cache1 (k-1) (s-w) dem1
                  result = v1 + v2
                  cache' = Map.insert (k, s) result cache2
              in (result, cache', dem2)
      (result, _, demanded) = go Map.empty n target Set.empty
  in (result, demanded)

-- | Count demanded states per level
demandedPerLevel :: Set.Set (Int, Int) -> Int -> [Int]
demandedPerLevel demanded n =
  [Set.size (Set.filter (\(k, _) -> k == level) demanded) | level <- [0..n]]

-- | Full DP: count ALL reachable (level, value) states
fullDPStates :: [Int] -> Int -> [Int]  -- states per level
fullDPStates weights target =
  let go reachable [] level acc = acc ++ [IS.size reachable]
      go reachable (w:ws) level acc =
        let new = IS.union reachable (IS.map (+w) (IS.filter (<= target - w) reachable))
            -- Only keep states ≤ target
            filtered = IS.filter (<= target) new
        in go filtered ws (level + 1) (acc ++ [IS.size reachable])
  in go (IS.singleton 0) weights 0 []

-- | Modular fusion: how many DISTINCT residues at each level?
modularFusion :: [Int] -> Int -> Int -> [Int]  -- states per level mod M
modularFusion weights target modulus =
  let go reachable [] acc = acc ++ [IS.size reachable]
      go reachable (w:ws) acc =
        let new = IS.union reachable (IS.map (\s -> (s + w) `mod` modulus) reachable)
        in go new ws (acc ++ [IS.size reachable])
  in go (IS.singleton 0) weights []

-- | For a given modulus M, check: does reducing mod M preserve the answer?
-- Compare: is T reachable (exact) vs is (T mod M) reachable (modular)
modularPreservesAnswer :: [Int] -> Int -> Int -> (Bool, Bool, Bool)
-- Returns: (exact_answer, modular_answer, preserved)
modularPreservesAnswer weights target modulus =
  let -- Exact DP
      exact = IS.member target $ foldl' (\acc w ->
        IS.union acc (IS.map (+w) acc)) (IS.singleton 0) weights
      -- Modular DP
      modular = IS.member (target `mod` modulus) $ foldl' (\acc w ->
        IS.union acc (IS.map (\s -> (s + w) `mod` modulus) acc)) (IS.singleton 0) weights
  in (exact, modular, exact == modular || (not exact && modular))
     -- modular can have false positives (modular=True when exact=False)
     -- but NOT false negatives (if exact=True, modular must be True)

-- | Search for BEST modulus: smallest M where modular answer = exact answer
-- for this specific instance
findBestModulus :: [Int] -> Int -> [(Int, Bool)]
findBestModulus weights target =
  let exact = IS.member target $ foldl' (\acc w ->
        IS.union acc (IS.map (+w) acc)) (IS.singleton 0) weights
  in [(m, let (_, modAns, _) = modularPreservesAnswer weights target m
          in modAns == exact)
     | m <- [2..200]]

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
  putStrLn " TREE FUSION: can we collapse the 2^n recursion tree?"
  putStrLn " coeff(k,s) = coeff(k-1,s) + coeff(k-1,s-w_k)"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Demand tree vs full DP vs 2^n
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. DEMAND TREE: top-down demanded states vs full DP ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 12 "demanded"
    ++ padR 12 "full-DP" ++ padR 10 "2^n" ++ padR 10 "dem/2^n"
  putStrLn (replicate 56 '-')
  mapM_ (\n -> do
    -- YES
    let (wsY, tY) = mkHashYes n
        (_, demY) = demandCoeff wsY tY
        demSizeY = Set.size demY
        fullY = sum (fullDPStates wsY tY)
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 12 (show demSizeY)
      ++ padR 12 (show fullY)
      ++ padR 10 (show ((2::Int)^n))
      ++ padR 10 (showF 3 (fromIntegral demSizeY / fromIntegral ((2::Int)^n) :: Double))
    -- NO
    let (wsN, tN) = mkHash n
        (_, demN) = demandCoeff wsN tN
        demSizeN = Set.size demN
        fullN = sum (fullDPStates wsN tN)
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 12 (show demSizeN)
      ++ padR 12 (show fullN)
      ++ padR 10 (show ((2::Int)^n))
      ++ padR 10 (showF 3 (fromIntegral demSizeN / fromIntegral ((2::Int)^n) :: Double))
    ) [6, 8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Demand tree shape — states per level
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. DEMAND TREE SHAPE: states demanded per level (n=10) ==="
  putStrLn ""
  let (ws2, t2) = mkHashYes 10
      (_, dem2) = demandCoeff ws2 t2
      perLevel2 = demandedPerLevel dem2 10
      full2 = fullDPStates ws2 t2
  putStrLn $ padR 8 "level" ++ padR 12 "demanded" ++ padR 12 "full-DP"
    ++ padR 10 "2^level"
  putStrLn (replicate 42 '-')
  mapM_ (\(lvl, dem, full) ->
    putStrLn $ padR 8 (show lvl) ++ padR 12 (show dem) ++ padR 12 (show full)
      ++ padR 10 (show ((2::Int)^lvl))
    ) (zip3 [0..10::Int] perLevel2 (full2 ++ repeat 0))
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Modular fusion — how many states with mod M?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. MODULAR FUSION: DP states mod M (n=10) ==="
  putStrLn "   (if M states ≈ M for all levels → full saturation, no fusion)"
  putStrLn ""
  let (ws3, t3) = mkHash 10
  putStrLn $ padR 5 "M" ++ padR 12 "peak-states" ++ padR 12 "M"
    ++ padR 12 "peak/M" ++ padR 10 "correct"
  putStrLn (replicate 52 '-')
  mapM_ (\m -> do
    let states = modularFusion ws3 t3 m
        peak = maximum states
        (_, _, preserved) = modularPreservesAnswer ws3 t3 m
    putStrLn $ padR 5 (show m)
      ++ padR 12 (show peak)
      ++ padR 12 (show m)
      ++ padR 12 (showF 2 (fromIntegral peak / fromIntegral m :: Double))
      ++ padR 10 (if preserved then "YES" else "FP!")
    ) [3, 7, 13, 29, 53, 97, 197, 499, 997]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: Best modulus search — find M that preserves answer
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. MODULUS SEARCH: smallest M that gives correct NO ==="
  putStrLn "   (for NO instances: need a modulus where false positive doesn't occur)"
  putStrLn ""
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        results = findBestModulus ws t
        correct = filter snd results
        incorrect = filter (not . snd) results
    putStrLn $ "  n=" ++ show n ++ " target=" ++ show t
    if null incorrect
      then putStrLn "    ALL moduli 2..200 give correct answer (target may be reachable)"
      else do
        let firstCorrect = head (filter snd results)
            numFP = length (takeWhile (not . snd) results)
        putStrLn $ "    First correct modulus: M=" ++ show (fst firstCorrect)
          ++ " (" ++ show numFP ++ " false positives before it)"
        putStrLn $ "    False positive moduli: "
          ++ show (take 15 (map fst (filter (not . snd) results)))
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: THE FUSION RATIO — the key scaling metric
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. FUSION RATIO: demanded / 2^n ==="
  putStrLn "   dem/2^n → 0 : demand tree is MUCH smaller → hope!"
  putStrLn "   dem/2^n → 1 : every state is demanded → no fusion"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "demanded" ++ padR 10 "2^n"
    ++ padR 12 "ratio" ++ padR 12 "dem/n²"
  putStrLn (replicate 52 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
        (_, dem) = demandCoeff ws t
        demSize = Set.size dem
        twoN = (2::Int)^n
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show demSize)
      ++ padR 10 (show twoN)
      ++ padR 12 (showF 4 (fromIntegral demSize / fromIntegral twoN :: Double))
      ++ padR 12 (showF 1 (fromIntegral demSize / fromIntegral (n*n) :: Double))
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "ANALYSIS:"
  putStrLn " The demand tree shows how many UNIQUE states the recursion visits."
  putStrLn " If demanded << 2^n, the tree has natural FUSION (collisions)."
  putStrLn " If demanded ≈ 2^n, every path is unique — no shortcuts."
  putStrLn ""
  putStrLn " For density-1: weights are ~2^n, so T-w₁-w₃ ≠ T-w₂-w₄ almost"
  putStrLn " always. No collisions → no fusion → 2^n is unavoidable."
  putStrLn ""
  putStrLn " For structured weights: collisions happen naturally → fewer states."
  putStrLn " The P vs NP gap: can we FORCE collisions (via algebraic rewriting)"
  putStrLn " where they don't exist naturally?"
  putStrLn "═══════════════════════════════════════════════════════════════════"
