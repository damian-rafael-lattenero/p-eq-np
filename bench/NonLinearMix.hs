module Main where

{-
  NON-LINEAR MIXING: the one thing we haven't tried.

  All previous transforms preserved entropy:
  - Scalar multiply: permutes residues, same count
  - Base change: redistributes entropy, same total
  - Oracle: projects onto modular residues, lossy

  Non-linear mixing: COMBINE weights together, creating new weights
  whose bit patterns are ENTANGLED with the originals. This can
  DESTROY entropy if the mixing creates collisions (interference).

  Key constraint: the transformation must preserve solvability.
  If Σ x_i w_i = T has solution x*, the transformed problem must
  also have a detectable solution.

  APPROACH 1: Pairwise sums
    Replace n weights with n(n-1)/2 pairwise sums w_i + w_j.
    New problem: find a CLIQUE of pairs that corresponds to a subset.
    Pro: pairwise sums have fewer distinct values (collisions!).
    Con: the clique constraint is itself hard.

  APPROACH 2: XOR mixing (already in BitDecompose)
    Replace w_i with w_i XOR w_j. Changes bit patterns non-linearly.
    But doesn't preserve subset sum (different problem).

  APPROACH 3: Modular folding
    Replace w_i with (w_i mod M, w_i div M) — split into two parts.
    Solve the low part (mod M) and high part (div M) separately.
    Cross-check: solutions must agree on which weights are included.
    If M = √(max_weight): each part has √ the range → √ the entropy.
    The COUPLING between parts is the hard part (again).

  APPROACH 4: Random linear combinations (lattice idea)
    Choose random vectors r_1, ..., r_k ∈ {0,1}^n.
    Compute "mixed weights" m_j = Σ_i r_j_i × w_i (random sums of weights).
    If x* is a solution: Σ_i x*_i × w_i = T, so for each r_j:
      Σ_i (x*_i AND r_j_i) × w_i = some known value? NO — depends on x*.
    This doesn't directly help. But the DISTRIBUTION of mixed weights
    might reveal structure about x*.

  APPROACH 5: The "folding" idea — reduce the problem size
    Split weights into two halves A, B.
    For each pair (a ∈ subsets(A), b ∈ subsets(B)):
      if sum(a) + sum(b) = T → solution.
    This is MITM. But what if we FOLD more aggressively?
    Split into √n groups of √n weights each.
    Each group has 2^√n reachable sums.
    Now the problem is: find one sum per group that totals T.
    This is a NEW Subset Sum on √n "weights" (the group sums),
    each from a set of 2^√n choices.
    Can we solve THIS instance more efficiently?

  LET'S MEASURE: for approach 3 (modular folding), does splitting
  the weights into (low, high) parts reduce the decoherence in each part?
  And can we recombine cheaply?
-}

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Bits (xor, shiftR, testBit)
import PeqNP.ActorSolver (padR)

-- ═══════════════════════════════════════════════════════════
-- Approach 3: Modular Folding
-- Split each weight into (w mod M, w div M).
-- The low parts live in [0, M). The high parts live in [0, max/M).
-- Solve low and high INDEPENDENTLY, then cross-check coupling.
-- ═══════════════════════════════════════════════════════════

-- | For a given modulus M, measure the decoherence of the
-- LOW parts (w_i mod M) and HIGH parts (w_i div M) separately.
-- Returns (low_distinct_sums, high_distinct_sums, total_2^n)
foldingAnalysis :: Int -> [Int] -> (Int, Int, Int)
foldingAnalysis m weights =
  let n = length weights
      numSubsets = (2::Int)^n
      lowParts  = map (`mod` m) weights
      highParts = map (`div` m) weights

      allLowSums  = Set.fromList [subsetSum mask lowParts  | mask <- [0..numSubsets-1]]
      allHighSums = Set.fromList [subsetSum mask highParts | mask <- [0..numSubsets-1]]
  in (Set.size allLowSums, Set.size allHighSums, numSubsets)
  where
    subsetSum mask ws = sum [w | (i,w) <- zip [0..] ws, testBit mask i]

-- | Cross-check: how many (low_sum, high_sum) pairs exist?
-- If this is much less than low × high → coupling is strong.
-- If this equals min(2^n, low × high) → coupling is weak.
foldingCoupling :: Int -> [Int] -> (Int, Int, Int, Int)
  -- Returns (joint_pairs, low_distinct, high_distinct, 2^n)
foldingCoupling m weights =
  let n = length weights
      numSubsets = (2::Int)^n
      lowParts  = map (`mod` m) weights
      highParts = map (`div` m) weights

      jointPairs = Set.fromList
        [ (subsetSum mask lowParts, subsetSum mask highParts)
        | mask <- [0..numSubsets-1]
        ]
      lowDistinct  = Set.size $ Set.map fst jointPairs
      highDistinct = Set.size $ Set.map snd jointPairs
  in (Set.size jointPairs, lowDistinct, highDistinct, numSubsets)
  where
    subsetSum mask ws = sum [w | (i,w) <- zip [0..] ws, testBit mask i]

-- ═══════════════════════════════════════════════════════════
-- Approach 5: Group folding (recursive MITM)
-- Split into g groups of n/g weights.
-- Each group has up to 2^(n/g) reachable sums.
-- New problem: pick one sum per group, total = T.
-- ═══════════════════════════════════════════════════════════

-- | Split weights into g groups, compute reachable sums per group.
-- Returns: list of (group_size, num_reachable_sums)
groupFolding :: Int -> [Int] -> [(Int, Int)]
groupFolding g weights =
  let n = length weights
      groupSize = (n + g - 1) `div` g
      groups = chunk groupSize weights
  in map (\grp ->
    let sums = Set.fromList [subsetSum mask grp | mask <- [0..(2::Int)^length grp - 1]]
    in (length grp, Set.size sums)
    ) groups
  where
    subsetSum mask ws = sum [w | (i,w) <- zip [0..] ws, testBit mask i]

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk k xs = let (a, b) = splitAt k xs in a : chunk k b

-- ═══════════════════════════════════════════════════════════

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
  putStrLn " NON-LINEAR MIXING: can we destroy entropy?"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  let n = 14
      (ws, t) = mkHash n
      numSub = (2::Int)^n
  putStrLn $ "Instance: HASH n=" ++ show n ++ ", 2^n=" ++ show numSub
  putStrLn ""

  -- Part 1: Modular folding — split at various M
  putStrLn "=== MODULAR FOLDING: split w_i into (w mod M, w div M) ==="
  putStrLn (padR 10 "M" ++ padR 12 "low-sums" ++ padR 12 "high-sums"
    ++ padR 12 "joint" ++ padR 12 "low×high" ++ padR 10 "coupling")
  putStrLn (replicate 68 '-')
  mapM_ (\m -> do
    let (joint, lowD, highD, _) = foldingCoupling m ws
        product' = lowD * highD
        coupling = fromIntegral joint / fromIntegral (min numSub product') :: Double
    putStrLn $ padR 10 (show m)
      ++ padR 12 (show lowD)
      ++ padR 12 (show highD)
      ++ padR 12 (show joint)
      ++ padR 12 (show product')
      ++ padR 10 (showF 1 (coupling * 100) ++ "%")
    ) [2, 4, 16, 64, 128, 256, 512, 1024, 4096]
  putStrLn "  coupling% = joint / min(2^n, low×high). Low = weak coupling = good!"
  putStrLn ""

  -- Part 2: Group folding — split into groups
  putStrLn "=== GROUP FOLDING: split into g groups of n/g weights ==="
  mapM_ (\g -> do
    let groups = groupFolding g ws
        totalGroupSums = product [snd grp | grp <- groups]
        reductionVsExponential = fromIntegral totalGroupSums / fromIntegral numSub :: Double
    putStrLn $ "  g=" ++ show g ++ " groups:"
    mapM_ (\(i, (sz, sums)) ->
      putStrLn $ "    group " ++ show i ++ ": " ++ show sz
        ++ " weights → " ++ show sums ++ " reachable sums"
      ) (zip [1::Int ..] groups)
    putStrLn $ "    Product of group sums: " ++ show totalGroupSums
      ++ " (vs 2^n=" ++ show numSub ++ ")"
    putStrLn $ "    Ratio: " ++ showF 1 reductionVsExponential ++ "x"
    putStrLn $ "    NEW problem: pick 1 sum from each of " ++ show g
      ++ " groups, total = " ++ show t
    putStrLn ""
    ) [2, 4, 7, 14]

  -- Part 3: The recursive question
  putStrLn "=== THE RECURSIVE IDEA ==="
  putStrLn "  Split n=14 into 7 pairs. Each pair has ≤4 sums."
  let pairs = groupFolding 7 ws
  putStrLn $ "  Group sums: " ++ show [snd p | p <- pairs]
  let newWeightSets = [ [subsetSum mask grp | mask <- [0..(2::Int)^length grp - 1]]
                       | grp <- chunk 2 ws]
  putStrLn $ "  New 'weight sets' per group: " ++ show (map (take 4) newWeightSets)
  putStrLn ""
  putStrLn "  This is now: choose one value from each of 7 sets,"
  putStrLn "  such that they sum to T. A 'multi-choice Subset Sum'."
  putStrLn ""
  putStrLn "  Each set has ≤ 4 values. Total combinations: 4^7 = 16384 = 2^14."
  putStrLn "  No savings vs brute force!!"
  putStrLn ""
  putStrLn "  But with √n groups of √n: each has 2^√n sums."
  putStrLn "  Total: (2^√n)^√n = 2^n. Same!!"
  putStrLn ""
  putStrLn "  UNLESS: the multi-choice problem has structure we can exploit."
  putStrLn "  Let's check: do the group sums have COLLISIONS?"
  putStrLn ""

  -- Check collisions in group sums
  let sqrtGroups = groupFolding (round (sqrt (fromIntegral n) :: Double)) ws
  putStrLn $ "  √n ≈ " ++ show (round (sqrt (fromIntegral n) :: Double) :: Int)
    ++ " groups:"
  mapM_ (\(i, (sz, sums)) ->
    putStrLn $ "    group " ++ show i ++ ": " ++ show sz
      ++ " weights → " ++ show sums ++ " distinct sums"
      ++ " (max=" ++ show ((2::Int)^sz) ++ ", collision="
      ++ show ((2::Int)^sz - sums) ++ ")"
    ) (zip [1::Int ..] sqrtGroups)
  putStrLn ""

  -- Part 4: The key measurement for non-linear mixing
  -- If we XOR pairs of weights, does the decoherence change?
  putStrLn "=== XOR MIXING: w'_i = w_i XOR w_{i+1} ==="
  let xorWeights = zipWith xor ws (tail ws ++ [head ws])
  putStrLn $ "  Original weights[0..3]:  " ++ show (take 4 ws)
  putStrLn $ "  XOR-mixed weights[0..3]: " ++ show (take 4 xorWeights)
  let origDistinct = Set.size $ Set.fromList
        [subsetSum mask ws | mask <- [0..numSub-1]]
      xorDistinct = Set.size $ Set.fromList
        [subsetSum mask xorWeights | mask <- [0..numSub-1]]
  putStrLn $ "  Original distinct sums:  " ++ show origDistinct ++ " / " ++ show numSub
  putStrLn $ "  XOR-mixed distinct sums: " ++ show xorDistinct ++ " / " ++ show numSub
  putStrLn $ "  Entropy change: "
    ++ if xorDistinct < origDistinct
       then show (origDistinct - xorDistinct) ++ " FEWER distinct sums! Entropy reduced!"
       else if xorDistinct > origDistinct
       then show (xorDistinct - origDistinct) ++ " MORE distinct sums."
       else "SAME."
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"

subsetSum :: Int -> [Int] -> Int
subsetSum mask ws = sum [w | (i,w) <- zip [0..] ws, testBit mask i]

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int) / fromIntegral factor :: Double
  in show rounded
