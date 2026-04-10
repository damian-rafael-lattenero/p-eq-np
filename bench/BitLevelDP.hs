module Main where

-- BIT-LEVEL DP v2: combined carry + GF(2) constraint propagation
--
-- v1 showed: uncoupled carry DP has 85% false positive rate.
--            GF(2) without carries has 100% false negative rate.
--
-- v2 combines BOTH: at each bit level, track (carry, GF2_matrix).
-- The GF(2) equations encode WHICH items must be selected,
-- while the carry tracks HOW MANY. Together they should be tighter.
--
-- KEY QUESTION: how many combined states survive at each level?
--   O(n)   → polynomial algorithm exists
--   2^n    → coupling is the real barrier
--   O(n^k) → intermediate complexity

import qualified Data.Set as Set
import Data.List (foldl')
import Data.Bits (xor, shiftR, testBit, setBit, (.&.), countTrailingZeros, shiftL)
import PeqNP.BitDecompose (bitLevelSolve, BitLevelStats(..))
import PeqNP.ActorSolver (padR)

-- ════════════════════════════════════════════
-- GF(2) REDUCED MATRIX
-- ════════════════════════════════════════════

-- Sorted list of (pivot_column, row_bitset).
-- Row bitset: bits 0..n-1 = variable coefficients, bit n = rhs.
-- Matrix is in reduced row echelon form (RREF).
type GF2Mat = [(Int, Int)]

-- | Add a row to the RREF matrix.
-- Returns Nothing if the new equation contradicts existing ones.
gf2Add :: Int -> Int -> GF2Mat -> Maybe GF2Mat
gf2Add n newRow mat =
  let varMask = (1 `shiftL` n) - 1
      -- Reduce by existing pivots
      reduced = foldl' (\r (col, piv) ->
        if testBit r col then r `xor` piv else r) newRow mat
      vars = reduced .&. varMask
  in if vars == 0
     then if testBit reduced n then Nothing   -- 0 = 1 → inconsistent
          else Just mat                        -- 0 = 0 → redundant
     else let pivCol = countTrailingZeros vars
              -- Maintain RREF: clear new pivot col in existing rows
              mat' = map (\(c, r) ->
                if testBit r pivCol then (c, r `xor` reduced) else (c, r)) mat
          in Just (insertSorted (pivCol, reduced) mat')

insertSorted :: (Int, Int) -> [(Int, Int)] -> [(Int, Int)]
insertSorted p [] = [p]
insertSorted p@(c, _) (q@(c', _) : rest)
  | c < c'    = p : q : rest
  | otherwise  = q : insertSorted p rest

-- | Build the GF(2) row for bit level j: variable bits + rhs bit.
mkGF2Row :: [Int] -> Int -> Int -> Int -> Int
mkGF2Row weights lvl rhs n =
  let v = foldl' (\acc (i, w) ->
            if testBit w lvl then setBit acc i else acc) 0 (zip [0..] weights)
  in if rhs == 1 then setBit v n else v

-- ════════════════════════════════════════════
-- COMBINED CARRY + GF(2) DP
-- ════════════════════════════════════════════

-- State: (carry_value, GF2_matrix_in_RREF)
-- Ord derived lexicographically → works for Set dedup.
type CState = (Int, GF2Mat)

-- | Run the combined DP. Returns (prediction, states_per_level, peak_states, overflowed).
combinedDP :: Int -> [Int] -> Int -> (Bool, [Int], Int, Bool)
combinedDP maxSt weights target =
  let n  = length weights
      bw = bitWidth (max (abs target) (maximum (map abs weights)))
  in go 0 (Set.singleton (0 :: Int, [] :: GF2Mat)) []
  where
    n  = length weights
    bw = bitWidth (max (abs target) (maximum (map abs weights)))

    go :: Int -> Set.Set CState -> [Int] -> (Bool, [Int], Int, Bool)
    go j states acc
      | Set.null states = (False, reverse acc, maxList acc, False)
      | j > bw =
          let ok = any (\(c, _) -> c == 0) (Set.toList states)
          in (ok, reverse (Set.size states : acc), maxList (Set.size states : acc), False)
      | Set.size states > maxSt =
          (False, reverse (Set.size states : acc), maxList (Set.size states : acc), True)
      | otherwise =
          let tj    = if testBit target j then 1 else 0
              onesJ = length [w | w <- weights, testBit w j]
              next  = Set.fromList
                [ (cOut, mat')
                | (cIn, mat) <- Set.toList states
                , let rhs = (tj + cIn) `mod` 2
                      row = mkGF2Row weights j rhs n
                , Just mat' <- [gf2Add n row mat]
                , k <- [0 .. onesJ]
                , (cIn + k) `mod` 2 == tj
                , let cOut = (cIn + k) `div` 2
                ]
          in go (j + 1) next (Set.size next : acc)

    maxList [] = 0
    maxList xs = maximum xs

-- ════════════════════════════════════════════
-- GROUND TRUTH
-- ════════════════════════════════════════════

dpReachable :: [Int] -> Set.Set Int
dpReachable = foldl' (\acc w -> Set.union acc (Set.map (+w) acc)) (Set.singleton 0)

-- ════════════════════════════════════════════
-- INSTANCES
-- ════════════════════════════════════════════

mix :: Int -> Int
mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
             x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
         in x2 `xor` (x2 `shiftR` 16)

mkDensity1 :: Int -> ([Int], Int)
mkDensity1 n =
  let ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
           | i <- [0..n-1 :: Int]]
  in (ws, sum ws `div` 2 + 1)

mkRand :: Int -> Int -> ([Int], Int)
mkRand n seed =
  let cap = min n 59
      ws = [2^cap + (abs (mix (i * 2654435761 + seed * 999983 + 0x12345))
            `mod` max 1 (2^(cap - 1)))
           | i <- [0..n-1 :: Int]]
      s = sum ws
      t = s `div` 3 + abs (mix (seed * 1000003)) `mod` max 1 (s `div` 3)
  in (ws, max 0 (min s t))

mkSafe :: Int -> ([Int], Int)
mkSafe n
  | n >= 60   = let ws = [n*n + abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (n*n)
                          | i <- [0..n-1]]
                in (ws, sum ws `div` 2 + 1)
  | otherwise = mkDensity1 n

yesTarget :: [Int] -> Int -> Int
yesTarget ws n = sum (take (n `div` 2) ws)

bitWidth :: Int -> Int
bitWidth x = go (abs x) 0
  where go 0 acc = max 1 acc
        go v acc = go (v `shiftR` 1) (acc + 1)

-- ════════════════════════════════════════════
-- MAIN
-- ════════════════════════════════════════════

main :: IO ()
main = do
  putStrLn "══════════════════════════════════════════════════════════════"
  putStrLn " BIT-LEVEL DP v2: carry + GF(2) combined"
  putStrLn "══════════════════════════════════════════════════════════════"
  putStrLn ""
  experiment1
  experiment2
  experiment3
  experiment4
  experiment5
  finalWords

-- ════════════════════════════════════════════
-- EXP 1: Carry-only scaling (confirm O(n), up to n=200)
-- ════════════════════════════════════════════

experiment1 :: IO ()
experiment1 = do
  putStrLn "┌──────────────────────────────────────────────────────┐"
  putStrLn "│ EXP 1: CARRY-ONLY SCALING (uncoupled, baseline)     │"
  putStrLn "└──────────────────────────────────────────────────────┘"
  putStrLn ""
  putStrLn (padR 6 "n" ++ padR 8 "bits" ++ padR 12 "max_carry"
    ++ padR 10 "n/2+1" ++ padR 10 "predict")
  putStrLn (replicate 48 '-')
  mapM_ (\n -> do
    let (ws, t) = mkSafe n
        st = bitLevelSolve ws t
    putStrLn $ padR 6 (show n) ++ padR 8 (show (blsBitsUsed st))
      ++ padR 12 (show (blsMaxCarry st))
      ++ padR 10 (show (n `div` 2 + 1))
      ++ padR 10 (if blsFound st then "YES" else "NO")
    ) [8, 12, 16, 20, 30, 50, 100, 200]
  putStrLn ""

-- ════════════════════════════════════════════
-- EXP 2: Combined DP state counts
-- ════════════════════════════════════════════

experiment2 :: IO ()
experiment2 = do
  putStrLn "┌──────────────────────────────────────────────────────┐"
  putStrLn "│ EXP 2: COMBINED (carry + GF2) STATE COUNTS          │"
  putStrLn "│                                                       │"
  putStrLn "│ O(n) → poly algorithm. 2^n → coupling is barrier.   │"
  putStrLn "└──────────────────────────────────────────────────────┘"
  putStrLn ""

  mapM_ (\n -> do
    let (ws, tNo) = mkDensity1 n
        tYes = yesTarget ws n
        cap = 100000
        (predNo, trNo, peakNo, ovNo)   = combinedDP cap ws tNo
        (predYes, trYes, peakYes, ovYes) = combinedDP cap ws tYes
    putStrLn $ "  n=" ++ show n ++ " (NO target):"
      ++ " predict=" ++ show predNo
      ++ " peak_states=" ++ show peakNo
      ++ if ovNo then " OVERFLOW" else ""
    putStrLn $ "    trace: " ++ showTrace trNo
    putStrLn $ "  n=" ++ show n ++ " (YES target):"
      ++ " predict=" ++ show predYes
      ++ " peak_states=" ++ show peakYes
      ++ if ovYes then " OVERFLOW" else ""
    putStrLn $ "    trace: " ++ showTrace trYes
    putStrLn ""
    ) [6, 8, 10, 12, 14]

showTrace :: [Int] -> String
showTrace xs
  | length xs <= 20 = unwords (map show xs)
  | otherwise = unwords (map show (take 10 xs))
                ++ " ... " ++ unwords (map show (takeLast 5 xs))
  where takeLast k = reverse . take k . reverse

-- ════════════════════════════════════════════
-- EXP 3: Accuracy on random instances
-- ════════════════════════════════════════════

experiment3 :: IO ()
experiment3 = do
  putStrLn "┌──────────────────────────────────────────────────────┐"
  putStrLn "│ EXP 3: ACCURACY — combined vs carry-only vs exact   │"
  putStrLn "│                                                       │"
  putStrLn "│ 100 random density-1 instances per n.                │"
  putStrLn "└──────────────────────────────────────────────────────┘"
  putStrLn ""
  putStrLn (padR 5 "n" ++ padR 10 "exact-Y"
    ++ padR 12 "carry-FP" ++ padR 12 "combo-FP"
    ++ padR 12 "combo-FN" ++ padR 12 "combo-OV")
  putStrLn (replicate 64 '-')

  mapM_ (\n -> do
    let trials = 100
        cap = 50000
        results = [ let (ws, t) = mkRand n seed
                        exact    = Set.member t (dpReachable ws)
                        carryP   = blsFound (bitLevelSolve ws t)
                        (comboP, _, _, ov) = combinedDP cap ws t
                    in (exact, carryP, comboP, ov)
                  | seed <- [1..trials] ]
        exactY  = length [() | (True, _, _, _)  <- results]
        carryFP = length [() | (False, True, _, _) <- results]
        comboFP = length [() | (False, _, True, _) <- results]
        comboFN = length [() | (True, _, False, _) <- results]
        comboOV = length [() | (_, _, _, True)    <- results]
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show exactY)
      ++ padR 12 (show carryFP)
      ++ padR 12 (show comboFP)
      ++ padR 12 (show comboFN)
      ++ padR 12 (show comboOV)
    ) [8, 10, 12, 14]
  putStrLn ""
  putStrLn "  carry-FP  = uncoupled carry says YES when NO (relaxation too loose)"
  putStrLn "  combo-FP  = combined says YES when NO  (should be lower)"
  putStrLn "  combo-FN  = combined says NO when YES  (should be 0 if no overflow)"
  putStrLn "  combo-OV  = state overflow (capped at 50k)"
  putStrLn ""

-- ════════════════════════════════════════════
-- EXP 4: Known YES/NO with detail
-- ════════════════════════════════════════════

experiment4 :: IO ()
experiment4 = do
  putStrLn "┌──────────────────────────────────────────────────────┐"
  putStrLn "│ EXP 4: KNOWN YES vs NO — detailed view              │"
  putStrLn "└──────────────────────────────────────────────────────┘"
  putStrLn ""
  putStrLn (padR 5 "n" ++ padR 8 "type"
    ++ padR 12 "carry" ++ padR 12 "combined"
    ++ padR 12 "exact" ++ padR 10 "peak-st")
  putStrLn (replicate 60 '-')

  mapM_ (\n -> do
    let (ws, tNo) = mkDensity1 n
        tYes = yesTarget ws n
        cap = 100000
        carryNo  = blsFound (bitLevelSolve ws tNo)
        carryYes = blsFound (bitLevelSolve ws tYes)
        (comboNo, _, pkNo, _)   = combinedDP cap ws tNo
        (comboYes, _, pkYes, _) = combinedDP cap ws tYes
        exactNo  = Set.member tNo (dpReachable ws)
        exactYes = Set.member tYes (dpReachable ws)
    putStrLn $ padR 5 (show n) ++ padR 8 "NO"
      ++ padR 12 (show carryNo)  ++ padR 12 (show comboNo)
      ++ padR 12 (show exactNo)  ++ padR 10 (show pkNo)
    putStrLn $ padR 5 (show n) ++ padR 8 "YES"
      ++ padR 12 (show carryYes) ++ padR 12 (show comboYes)
      ++ padR 12 (show exactYes) ++ padR 10 (show pkYes)
    ) [8, 10, 12, 14, 16]
  putStrLn ""

-- ════════════════════════════════════════════
-- EXP 5: Peak states scaling
-- ════════════════════════════════════════════

experiment5 :: IO ()
experiment5 = do
  putStrLn "┌──────────────────────────────────────────────────────┐"
  putStrLn "│ EXP 5: PEAK STATES SCALING (YES targets)            │"
  putStrLn "│                                                       │"
  putStrLn "│ How does peak_states grow with n?                    │"
  putStrLn "│ poly(n) → coupling is captured. 2^n → it's not.    │"
  putStrLn "└──────────────────────────────────────────────────────┘"
  putStrLn ""
  putStrLn (padR 6 "n" ++ padR 12 "peak_st"
    ++ padR 10 "2^n" ++ padR 10 "n^2"
    ++ padR 12 "peak/n^2" ++ padR 8 "OV?")
  putStrLn (replicate 60 '-')

  mapM_ (\n -> do
    let (ws, _) = mkDensity1 n
        tYes = yesTarget ws n
        cap = 200000
        (_, _, pk, ov) = combinedDP cap ws tYes
        r = if n > 0 then fromIntegral pk / fromIntegral (n * n) :: Double else 0
    putStrLn $ padR 6 (show n) ++ padR 12 (show pk)
      ++ padR 10 (show ((2::Int)^(min n 30)))
      ++ padR 10 (show (n*n))
      ++ padR 12 (showF 2 r)
      ++ padR 8 (if ov then "YES" else "no")
    ) [6, 8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

-- ════════════════════════════════════════════
-- CONCLUSIONS
-- ════════════════════════════════════════════

finalWords :: IO ()
finalWords = do
  putStrLn "══════════════════════════════════════════════════════════════"
  putStrLn " RESULTS"
  putStrLn ""
  putStrLn " 1. CARRY-ONLY: O(n) states, but 85% false positive rate."
  putStrLn "    The carry constraint alone is too weak."
  putStrLn ""
  putStrLn " 2. COMBINED (carry + GF2): tracks (carry, RREF_matrix)."
  putStrLn "    Each GF(2) equation uses the CORRECT rhs: (t_j + c_j) mod 2."
  putStrLn "    This prunes carry paths where the item-level constraints"
  putStrLn "    are inconsistent."
  putStrLn ""
  putStrLn " 3. STATE GROWTH tells us where the hardness lives:"
  putStrLn "    peak_states = O(n)   → carry + GF2 = full answer → P = NP"
  putStrLn "    peak_states = 2^Ω(n) → item coupling is the real barrier"
  putStrLn "    peak_states = n^O(1) → intermediate (subexponential?)"
  putStrLn ""
  putStrLn " THE DEEP STRUCTURE:"
  putStrLn "   The GF(2) equations at each bit level encode LINEAR"
  putStrLn "   constraints on the inclusion vector x. The carry encodes"
  putStrLn "   NONLINEAR constraints (integer division by 2). The"
  putStrLn "   interaction between linear and nonlinear constraints"
  putStrLn "   determines the state space growth — and the complexity"
  putStrLn "   of Subset Sum."
  putStrLn "══════════════════════════════════════════════════════════════"

-- ════════════════════════════════════════════
-- FORMATTING
-- ════════════════════════════════════════════

showF :: Int -> Double -> String
showF d x
  | isNaN x = "NaN"
  | isInfinite x = if x > 0 then "+Inf" else "-Inf"
  | otherwise =
      let f = 10.0 ^^ d :: Double
      in show (fromIntegral (round (x * f) :: Integer) / f)
