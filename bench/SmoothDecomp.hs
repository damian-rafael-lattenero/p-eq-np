module Main where

{-
  SMOOTH DECOMPOSITION: the "Number Field Sieve" for Subset Sum

  Core idea: a partial sum is "k-smooth" if it uses ≤ k weights.
  There are C(n, ≤k) smooth sums — polynomial for k = O(1),
  quasi-polynomial for k = O(log n).

  Algorithm:
    1. ENUMERATE all k-smooth partial sums (the "rainbow table")
       Each entry: (sum_value, bitmask_of_weights_used)
    2. COMBINE: find a set of smooth sums that:
       a) together sum to T
       b) use disjoint weight sets (each weight used at most once)
    3. The combination is itself a Subset Sum over smooth sums,
       but with COMPATIBILITY constraints (disjoint masks)

  This is like NFS: lift to "smooth elements", combine via algebra.
  The question: is the combination step tractable?

  Experiments:
    1. How many k-smooth sums exist for density-1?
    2. How many COMPATIBLE covers of T exist?
    3. Greedy + backtracking over smooth sums: how deep?
    4. Scaling: does this beat 2^{n/2} (MITM)?
-}

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import Data.List (foldl', sortBy, subsequences)
import Data.Ord (comparing, Down(..))
import Data.Bits (xor, shiftR, (.&.), (.|.), popCount, bit, zeroBits)
import PeqNP.ActorSolver (padR)

-- | A smooth partial sum: value + bitmask of which weights are used
data Smooth = Smooth
  { smValue :: !Int
  , smMask  :: !Int  -- bitmask: bit i set means weight i is included
  , smSize  :: !Int  -- number of weights used (popCount of mask)
  } deriving (Show, Eq, Ord)

-- | Enumerate all k-smooth partial sums (subsets of size ≤ k)
-- Returns map: sum_value → [Smooth] (multiple subsets can give same sum)
enumSmooth :: [Int] -> Int -> Map.Map Int [Smooth]
enumSmooth weights maxK =
  let n = length weights
      -- Generate all subsets of size ≤ maxK
      go :: Int -> Int -> Int -> Int -> Map.Map Int [Smooth] -> Map.Map Int [Smooth]
      go idx mask val size acc
        | size > maxK = acc
        | idx >= n    = if size > 0
                        then Map.insertWith (++) val [Smooth val mask size] acc
                        else acc
        | otherwise   =
            -- Skip this weight
            let acc1 = go (idx + 1) mask val size acc
                -- Include this weight
                acc2 = go (idx + 1) (mask .|. bit idx) (val + weights !! idx) (size + 1) acc1
            in if size > 0
               then Map.insertWith (++) val [Smooth val mask size] acc2
               else acc2
  in go 0 zeroBits 0 0 Map.empty

-- | Count total smooth sums
countSmooth :: Map.Map Int [Smooth] -> Int
countSmooth = Map.foldl' (\acc vs -> acc + length vs) 0

-- | Count distinct sum values
countDistinct :: Map.Map Int [Smooth] -> Int
countDistinct = Map.size

-- | GREEDY COMBINATION: find disjoint smooth sums that total to T
-- Strategy: pick the smooth sum closest to remaining target,
-- then recurse on the residual with compatible (disjoint) smooths.
greedyCombine :: Map.Map Int [Smooth] -> Int -> Int
               -> (Bool, Int, Int)  -- (found, nodes_explored, depth)
greedyCombine smoothMap target nWeights =
  let -- All smooth entries as a flat list, sorted by value descending
      allSmooth = sortBy (comparing (Down . smValue)) $
                  concatMap snd (Map.toList smoothMap)

      nodeLimit = 100000

      go :: Int -> Int -> Int -> Int -> (Bool, Int, Int)
      go remaining usedMask nodes depth
        | remaining == 0    = (True, nodes, depth)
        | remaining < 0     = (False, nodes, depth)
        | nodes >= nodeLimit = (False, nodes, depth)
        | otherwise =
            -- Find smooth sums that: (a) value ≤ remaining, (b) disjoint with usedMask
            let candidates = filter (\s -> smValue s <= remaining
                                       && (smMask s .&. usedMask) == 0) allSmooth
            in if null candidates then (False, nodes, depth)
               else tryList candidates remaining usedMask nodes depth

      tryList [] _ _ nodes depth = (False, nodes, depth)
      tryList (s:rest) remaining usedMask nodes depth =
        let newMask = usedMask .|. smMask s
            newRem  = remaining - smValue s
            (found, nodes', depth') = go newRem newMask (nodes + 1) (depth + 1)
        in if found then (True, nodes', depth')
           else tryList rest remaining usedMask nodes' depth
  in go target 0 0 0

-- | EXHAUSTIVE COMBINATION with pruning and NODE LIMIT (for correctness check)
exhaustiveCombine :: Map.Map Int [Smooth] -> Int -> Int -> Int -> (Bool, Int)
exhaustiveCombine smoothMap target _nWeights maxNodes =
  let allSmooth = sortBy (comparing (Down . smValue)) $
                  concatMap snd (Map.toList smoothMap)

      go remaining _usedMask nodes []     = (remaining == 0, nodes)
      go remaining usedMask nodes (s:rest)
        | nodes >= maxNodes = (False, nodes)  -- bail out
        | remaining < 0    = (False, nodes)
        | remaining == 0   = (True, nodes)
        | otherwise =
            let canUse = smValue s <= remaining && (smMask s .&. usedMask) == 0
                (foundIn, nodesIn) =
                  if canUse
                  then go (remaining - smValue s) (usedMask .|. smMask s) (nodes + 1) rest
                  else (False, nodes)
            in if foundIn then (True, nodesIn)
               else go remaining usedMask nodesIn rest
  in go target 0 0 allSmooth

-- | Brute force Subset Sum (for comparison)
bruteForce :: [Int] -> Int -> (Bool, Int)
bruteForce weights target =
  let n = length weights
      go rem idx nodes
        | rem == 0  = (True, nodes + 1)
        | rem < 0   = (False, nodes + 1)
        | idx >= n  = (False, nodes + 1)
        | otherwise =
            let w = weights !! idx
                (fIn, nIn) = go (rem - w) (idx + 1) (nodes + 1)
            in if fIn then (True, nIn) else go rem (idx + 1) nIn
  in go target 0 0

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
mkHashYes n =
  let (ws, _) = mkHash n
  in (ws, sum (take (n `div` 2) ws))

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int)
                / fromIntegral factor :: Double
  in show rounded

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn " SMOOTH DECOMPOSITION: the NFS analogy for Subset Sum"
  putStrLn " Precompute small-subset sums, combine to reach T"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: How many k-smooth sums exist?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. SMOOTH SUM CENSUS: C(n, ≤k) subsets ==="
  putStrLn "   k-smooth = uses ≤ k weights out of n"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "k=1" ++ padR 10 "k=2"
    ++ padR 10 "k=3" ++ padR 12 "k=log n" ++ padR 10 "2^n"
  putStrLn (replicate 58 '-')
  mapM_ (\n -> do
    let (ws, _) = mkHash n
        logN = max 1 (ceiling (logBase 2 (fromIntegral n) :: Double) :: Int)
        c k = countSmooth (enumSmooth ws k)
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show (c 1))
      ++ padR 10 (show (c 2))
      ++ padR 10 (show (c 3))
      ++ padR 12 (show (c logN) ++ " (k=" ++ show logN ++ ")")
      ++ padR 10 (show ((2::Int)^n))
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Coverage — what fraction of [0..T] is hit by smooth sums?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. COVERAGE: distinct sum values from k-smooth ==="
  putStrLn "   (high coverage → smooth sums are a good basis)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "target" ++ padR 10 "k=2"
    ++ padR 10 "k=3" ++ padR 12 "k=log n" ++ padR 12 "coverage%"
  putStrLn (replicate 56 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        logN = max 2 (ceiling (logBase 2 (fromIntegral n) :: Double) :: Int)
        sm = enumSmooth ws logN
        distinct = countDistinct sm
        coverage = fromIntegral distinct / fromIntegral (t + 1) * 100 :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show t)
      ++ padR 10 (show (countDistinct (enumSmooth ws 2)))
      ++ padR 10 (show (countDistinct (enumSmooth ws 3)))
      ++ padR 12 (show distinct)
      ++ padR 12 (showF 2 coverage ++ "%")
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Can we COMBINE smooth sums to reach T?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. COMBINATION: disjoint smooth sums → T? ==="
  putStrLn "   (greedy + backtracking over smooth sums)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 8 "k" ++ padR 10 "found"
    ++ padR 12 "sm-nodes" ++ padR 12 "brute" ++ padR 10 "speedup"
  putStrLn (replicate 64 '-')
  mapM_ (\n -> do
    let logN = max 2 (ceiling (logBase 2 (fromIntegral n) :: Double) :: Int)
    -- YES instance
    let (wsY, tY) = mkHashYes n
        smY = enumSmooth wsY logN
        (foundY, smNodesY, _) = greedyCombine smY tY n
        (_, bruteY) = bruteForce wsY tY
        speedupY = if smNodesY == 0 then 0
                   else fromIntegral bruteY / fromIntegral (max 1 smNodesY) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES" ++ padR 8 (show logN)
      ++ padR 10 (show foundY)
      ++ padR 12 (show smNodesY)
      ++ padR 12 (show bruteY)
      ++ padR 10 (showF 1 speedupY ++ "x")
    -- NO instance
    let (wsN, tN) = mkHash n
        smN = enumSmooth wsN logN
        (foundN, smNodesN, _) = greedyCombine smN tN n
        (_, bruteN) = bruteForce wsN tN
        speedupN = if smNodesN == 0 then 0
                   else fromIntegral bruteN / fromIntegral (max 1 smNodesN) :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO" ++ padR 8 (show logN)
      ++ padR 10 (show foundN)
      ++ padR 12 (show smNodesN)
      ++ padR 12 (show bruteN)
      ++ padR 10 (showF 1 speedupN ++ "x")
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: Exhaustive verification for small n
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. CORRECTNESS: exhaustive smooth combination (max 50k nodes) ==="
  putStrLn ""
  mapM_ (\n -> do
    let logN = max 2 (ceiling (logBase 2 (fromIntegral n) :: Double) :: Int)
        nodeLimit = 50000
    -- YES with k=logN
    let (wsY, tY) = mkHashYes n
        smY = enumSmooth wsY logN
        (exFoundY, exNodesY) = exhaustiveCombine smY tY n nodeLimit
    putStr $ "  n=" ++ show n ++ " k=" ++ show logN
      ++ " YES: found=" ++ show exFoundY
      ++ " nodes=" ++ show exNodesY
    -- Also with k=n/2 (but capped)
    let smY' = enumSmooth wsY (min (n `div` 2) 4)
        (exFoundY', exNodesY') = exhaustiveCombine smY' tY n nodeLimit
    putStrLn $ " | k=" ++ show (min (n `div` 2) 4)
      ++ ": found=" ++ show exFoundY'
      ++ " nodes=" ++ show exNodesY'
    ) [6, 8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: The scaling question
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. SCALING: smooth-nodes vs brute-force vs MITM ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "smooth-n" ++ padR 12 "brute"
    ++ padR 12 "2^(n/2)" ++ padR 12 "sm/MITM"
  putStrLn (replicate 54 '-')
  mapM_ (\n -> do
    let logN = max 2 (ceiling (logBase 2 (fromIntegral n) :: Double) :: Int)
        (ws, t) = mkHash n
        sm = enumSmooth ws logN
        (_, smNodes, _) = greedyCombine sm t n
        (_, bruteNodes) = bruteForce ws t
        mitm = (2::Int)^(n `div` 2)
        ratio = fromIntegral smNodes / fromIntegral mitm :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show smNodes)
      ++ padR 12 (show bruteNodes)
      ++ padR 12 (show mitm)
      ++ padR 12 (showF 3 ratio)
    ) [6, 8, 10, 12, 14]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "ANALYSIS:"
  putStrLn " The smooth decomposition has TWO costs:"
  putStrLn "   1. ENUMERATION: C(n, ≤k) smooth sums — quasi-poly for k=log n"
  putStrLn "   2. COMBINATION: finding disjoint cover — this is the bottleneck"
  putStrLn ""
  putStrLn " If combination nodes << 2^(n/2): we beat MITM!"
  putStrLn " If combination nodes ≈ 2^n: smooth basis doesn't help"
  putStrLn " The dream: O(n^{O(log n)}) total — quasi-polynomial!"
  putStrLn "═══════════════════════════════════════════════════════════════════"
