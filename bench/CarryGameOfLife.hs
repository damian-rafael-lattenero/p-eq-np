module Main where

{-
  QUANTUM ANALOGY: Superposition, Interference & Collapse

  UNCOUPLED carry state = "superposition" — multiple subsets coexist
  behind the same carry value. The carry is the "wave function."

  MULTIPLICITY = how many distinct subsets produce the same carry
  at each bit position. This is the "entanglement" measure.

  If multiplicity is low → uncoupled ≈ coupled → easy
  If multiplicity is high → lots of hidden state → hard

  INTERFERENCE = when two subsets produce the same carry AND
  the same future carries. They "merge" — the coupling doesn't
  matter past that point. Like wave interference.

  DECOHERENCE POINTS = bit positions where different subsets
  with the same carry also produce the same carry at the next bit.
  These are "free" — no coupling cost.
-}

import PeqNP.BitDecompose (decomposeProblem, BitColumn(..), toBits, maxBits)
import PeqNP.ActorSolver (padR)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Bits (xor, shiftR, testBit)

-- | For each subset of weights, compute the carry at each bit position.
-- Returns: for each bit position, a Map from carry_value → number of subsets
-- that produce that carry.
--
-- This measures the MULTIPLICITY: how many subsets hide behind each carry.
-- WARNING: enumerates 2^n subsets. Only feasible for n ≤ 18.
carryMultiplicity :: [Int] -> Int -> [Map.Map Int Int]
carryMultiplicity elems target =
  let n = length elems
      b = maxBits elems
      targetBits = toBits b target
      numSubsets = 2^n

      -- For each subset (bitmask 0..2^n-1), compute partial sum
      -- then trace the carry through each bit position
      allCarryTraces :: [[Int]]  -- list of carry traces, one per subset
      allCarryTraces =
        [ traceCarries targetBits (subsetSum mask elems)
        | mask <- [0..numSubsets-1]
        ]

      -- Count multiplicities at each bit position
      multiplicities = [ Map.fromListWith (+) [(carry, 1 :: Int) | trace <- allCarryTraces, let carry = trace !! k]
                       | k <- [0..b]
                       ]
  in multiplicities
  where
    subsetSum :: Int -> [Int] -> Int
    subsetSum mask ws = sum [w | (i, w) <- zip [0..] ws, testBit mask i]

    -- Given target bits and a partial sum, compute carry at each bit position
    traceCarries :: [Bool] -> Int -> [Int]
    traceCarries tBits partialSum =
      let sumBits = [testBit partialSum k | k <- [0..length tBits - 1]]
          -- Carry propagation: carry_0 = 0
          -- At bit k: sum_k + carry_k: if this matches target_k, carry_{k+1} = borrow/carry
          -- Actually, we track the carry of the DIFFERENCE (target - partialSum)
          -- Simpler: just track carry_out = (carry_in + selected_ones) / 2
          -- But we're given the FULL partial sum, not per-column selections.
          -- For multiplicity, what matters is: the carry VALUE at each bit.
          --
          -- The carry at bit k = (partialSum - target) accumulated through bits 0..k-1
          -- More precisely: the carry state from the column-by-column processing.
      in scanl (\c k ->
          let sBit = if testBit partialSum k then 1 else 0 :: Int
              tBit = if k < length tBits && tBits !! k then 1 else 0
              -- carry_out = (carry_in + sBit - tBit) at this position
              -- But that's the difference carry, not the column carry.
              -- For column carry: carry = (carry_in + column_ones_selected) `div` 2
              -- We can't reconstruct column_ones_selected from just the total sum.
              -- Instead, let's use a different approach: track the "running difference"
              -- between partialSum and target, accumulated through bits.
              total = c + sBit - tBit
              -- The carry to next position:
              carryOut = if total >= 0 then total `div` 2 else (total - 1) `div` 2
          in carryOut
          ) 0 [0..length tBits - 1]

-- | Simpler approach: for each bit position k, compute the residue
-- of the partial sum modulo 2^(k+1). This captures all the information
-- that "flowed through" bits 0..k.
--
-- Two subsets S₁, S₂ with the same residue mod 2^(k+1) are
-- INDISTINGUISHABLE by bits 0..k — they have the same "carry history."
-- They can be merged (interference) without loss.
--
-- MULTIPLICITY at bit k = how many distinct subsets produce each
-- residue mod 2^(k+1).
residueMultiplicity :: [Int] -> Int -> [(Int, Int, Int)]
  -- Returns: [(bit_position, num_distinct_residues, max_multiplicity)]
residueMultiplicity elems target =
  let n = length elems
      b = maxBits elems
      numSubsets = (2::Int)^n

      -- All partial sums
      allSums = [sum [w | (i, w) <- zip [0..] elems, testBit mask i]
                | mask <- [0..numSubsets-1 :: Int]]

      -- For each bit position k: count distinct (sum mod 2^(k+1)) values
      -- and the maximum number of sums sharing the same residue
  in [ let modulus = 2^(k+1)
           residues = map (`mod` modulus) allSums
           counts = Map.fromListWith (+) [(r, 1 :: Int) | r <- residues]
           numDistinct = Map.size counts
           maxMult = maximum (Map.elems counts)
       in (k, numDistinct, maxMult)
     | k <- [0..min (b-1) 30]  -- cap to avoid huge moduli
     ]

-- Instance generators
mkHash :: Int -> ([Int], Int)
mkHash n =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
           | i <- [0..n-1 :: Int]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

mkLCG :: Int -> ([Int], Int)
mkLCG n =
  let ws = [2^n + ((i * 1103515245 + 12345) `mod` (2^(n-1))) | i <- [0..n-1]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " QUANTUM SUBSET SUM: superposition, interference, collapse"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: Residue multiplicity = "entanglement" measurement
  -- At each bit k: how many distinct residues (mod 2^{k+1}) exist
  -- among ALL 2^n subset sums?
  -- distinct_residues = number of "superposition branches"
  -- max_multiplicity = how many subsets "interfere" into one branch
  putStrLn "=== RESIDUE MULTIPLICITY: how many subsets share the same carry? ==="
  putStrLn ""

  -- Small example
  putStrLn "--- [3, 5, 7, 11, 13] target=19 ---"
  let ws1 = [3, 5, 7, 11, 13]
      t1 = 19
      rm1 = residueMultiplicity ws1 t1
  putStrLn (padR 6 "bit" ++ padR 14 "residues" ++ padR 14 "max-mult"
    ++ padR 14 "2^(k+1)" ++ padR 14 "ratio")
  putStrLn (replicate 62 '-')
  mapM_ (\(k, nd, mm) ->
    let modulus = (2::Int)^(k+1)
    in putStrLn $ padR 6 (show k)
      ++ padR 14 (show nd)
      ++ padR 14 (show mm)
      ++ padR 14 (show modulus)
      ++ padR 14 (showF 1 (fromIntegral nd / fromIntegral modulus * 100) ++ "%")
    ) rm1
  putStrLn ""

  -- LCG n=14 (structured)
  putStrLn "--- LCG n=14 (structured) ---"
  let (wsL, tL) = mkLCG 14
      rmL = residueMultiplicity wsL tL
  putStrLn (padR 6 "bit" ++ padR 14 "residues" ++ padR 14 "max-mult"
    ++ padR 14 "2^n=16384" ++ "superposition")
  putStrLn (replicate 62 '-')
  mapM_ (\(k, nd, mm) ->
    putStrLn $ padR 6 (show k)
      ++ padR 14 (show nd)
      ++ padR 14 (show mm)
      ++ padR 14 (show ((2::Int)^(k+1)))
      ++ show (round (fromIntegral ((2::Int)^14) / fromIntegral nd :: Double) :: Int) ++ ":1"
    ) (take 16 rmL)
  putStrLn ""

  -- HASH n=14 (random)
  putStrLn "--- HASH n=14 (random, hard) ---"
  let (wsH, tH) = mkHash 14
      rmH = residueMultiplicity wsH tH
  putStrLn (padR 6 "bit" ++ padR 14 "residues" ++ padR 14 "max-mult"
    ++ padR 14 "2^n=16384" ++ "superposition")
  putStrLn (replicate 62 '-')
  mapM_ (\(k, nd, mm) ->
    putStrLn $ padR 6 (show k)
      ++ padR 14 (show nd)
      ++ padR 14 (show mm)
      ++ padR 14 (show ((2::Int)^(k+1)))
      ++ show (round (fromIntegral ((2::Int)^14) / fromIntegral nd :: Double) :: Int) ++ ":1"
    ) (take 16 rmH)
  putStrLn ""

  -- Part 2: The collapse cost
  -- At which bit does the multiplicity become 1 (fully collapsed)?
  -- Before that: superposition. After: classical.
  putStrLn "=== WHERE DOES THE WAVE COLLAPSE? ==="
  putStrLn "  (Bit where residues = 2^n, meaning every subset is distinguishable)"
  putStrLn ""
  mapM_ (\(label, ws, t) -> do
    let n = length ws
        rm = residueMultiplicity ws t
        fullN = (2::Int)^n
        collapseAt = case [(k, nd) | (k, nd, _) <- rm, nd == fullN] of
                       ((k,_):_) -> Just k
                       []        -> Nothing
    putStrLn $ "  " ++ padR 20 label
      ++ "n=" ++ padR 4 (show n)
      ++ "collapse@bit=" ++ maybe "never(within range)" show collapseAt
      ++ "  (2^n=" ++ show fullN ++ ")"
    ) [ ("LCG n=10", fst (mkLCG 10), snd (mkLCG 10))
      , ("Hash n=10", fst (mkHash 10), snd (mkHash 10))
      , ("LCG n=12", fst (mkLCG 12), snd (mkLCG 12))
      , ("Hash n=12", fst (mkHash 12), snd (mkHash 12))
      , ("LCG n=14", fst (mkLCG 14), snd (mkLCG 14))
      , ("Hash n=14", fst (mkHash 14), snd (mkHash 14))
      , ("Sequential n=14", [1..14], sum [1..7])
      , ("[1..16]", [1..16], sum [1..8])
      ]
  putStrLn ""

  -- Part 3: Superposition ratio at the PEAK bit
  putStrLn "=== SUPERPOSITION RATIO at bit n (the critical bit) ==="
  putStrLn "  2^n subsets compressed into how many residues?"
  putStrLn (padR 5 "n" ++ padR 10 "2^n" ++ padR 14 "LCG-resid"
    ++ padR 14 "Hash-resid" ++ padR 12 "LCG-compr" ++ padR 12 "Hash-compr")
  putStrLn (replicate 70 '-')
  mapM_ (\n -> do
    let (wsL', _tL') = mkLCG n
        (wsH', _tH') = mkHash n
        rmL' = residueMultiplicity wsL' (snd (mkLCG n))
        rmH' = residueMultiplicity wsH' (snd (mkHash n))
        fullN = (2::Int)^n
        -- Residues at bit position n (the critical one)
        resL = case [nd | (k, nd, _) <- rmL', k == n] of (x:_) -> x; _ -> 0
        resH = case [nd | (k, nd, _) <- rmH', k == n] of (x:_) -> x; _ -> 0
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show fullN)
      ++ padR 14 (show resL)
      ++ padR 14 (show resH)
      ++ padR 12 (show (fullN `div` max 1 resL) ++ ":1")
      ++ padR 12 (show (fullN `div` max 1 resH) ++ ":1")
    ) [8, 10, 12, 14, 16]

  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn "Compression N:1 = how many subsets share one residue."
  putStrLn "If compression stays high as n grows → superposition helps!"
  putStrLn "If compression → 1:1 → every subset is unique → 2^n states."
  putStrLn "═══════════════════════════════════════════════════════════"

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int) / fromIntegral factor :: Double
  in show rounded
