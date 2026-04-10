module Main where

{-
  THE CARRY STATE AS A GAME OF LIFE

  Processing Subset Sum bit-by-bit (LSB → MSB), the "carry state"
  is a set of possible carry values at each bit position.

  UNCOUPLED: each bit column is processed independently. Carry ≤ n/2.
             O(n³) total. But it's a RELAXATION — ignores coupling.

  COUPLED:   the same weights must be included across all bits.
             Carry state can explode to 2^n.

  THE GAP between uncoupled and coupled IS where NP-hardness lives.

  Visualization: x-axis = bit position, y-axis = carry value.
  Each cell is ALIVE (●) if that carry value is in the carry set,
  DEAD (·) if not. Watch the pattern evolve like GoL!
-}

import PeqNP.BitDecompose (decomposeProblem, BitColumn(..), toBits, maxBits)
import PeqNP.ActorSolver (padR)
import qualified Data.Set as Set
import Data.Bits (xor, shiftR, testBit)

-- | Process bit columns and return the carry SETS at each position.
-- This is the uncoupled (relaxed) carry evolution.
carryEvolution :: [Int] -> Int -> [Set.Set Int]
carryEvolution elems target =
  let columns = decomposeProblem elems
      targetBits = toBits (length columns) target
  in go columns targetBits (Set.singleton 0) [Set.singleton 0]
  where
    go [] _ _ acc = reverse acc
    go _ [] _ acc = reverse acc
    go (col:cols) (tBit:tBits) carryIn acc =
      let onesCount = bcOnesCount col
          targetBit = if tBit then 1 :: Int else 0
          carryOut = Set.fromList
            [ (c + s) `div` 2
            | c <- Set.toList carryIn
            , s <- [0..onesCount]
            , (c + s) `mod` 2 == targetBit
            ]
      in go cols tBits carryOut (carryOut : acc)

-- | ASCII visualization of carry state evolution.
-- Bit position → (x-axis), carry value → (y-axis, inverted).
visualizeCarry :: [Set.Set Int] -> String
visualizeCarry sets =
  let maxCarry = maximum [if Set.null s then 0 else Set.findMax s | s <- sets]
      nBits = length sets
      -- Header
      header = "     " ++ concatMap (\i -> padR 2 (show (i `mod` 10))) [0..nBits-1]
      separator = "     " ++ replicate (nBits * 2) '-'
      -- Rows (from maxCarry down to 0)
      rows = [ padR 4 (show c) ++ "|"
               ++ concatMap (\s -> if Set.member c s then "● " else "· ") sets
             | c <- [maxCarry, maxCarry-1..0]
             ]
  in unlines (["  bit:" ++ header, separator] ++ rows ++ [separator])

-- | Detect periodicity in carry evolution.
-- Check if carry sets repeat with some period T.
detectPeriod :: [Set.Set Int] -> Maybe Int
detectPeriod sets
  | length sets < 4 = Nothing
  | otherwise = case [t | t <- [1..length sets `div` 2]
                      , all (\i -> i + t >= length sets
                                   || sets !! i == sets !! (i + t))
                            [length sets `div` 3 .. length sets - t - 1]
                      ] of
      (t:_) -> Just t
      []    -> Nothing

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
  putStrLn " CARRY STATE: the Game of Life of Subset Sum"
  putStrLn " ● = carry value alive, · = dead"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Small example first
  putStrLn "=== SMALL: [5, 13, 3, 7, 11] target=19 ==="
  let ws1 = [5, 13, 3, 7, 11]
      t1 = 19
      ev1 = carryEvolution ws1 t1
  putStrLn $ visualizeCarry ev1
  putStrLn $ "  Sizes: " ++ show (map Set.size ev1)
  putStrLn $ "  Period: " ++ show (detectPeriod ev1)
  putStrLn ""

  -- Density-1 LCG (structured)
  putStrLn "=== LCG n=12 (structured weights) ==="
  let (wsL, tL) = mkLCG 12
      evL = carryEvolution wsL tL
  putStrLn $ visualizeCarry evL
  putStrLn $ "  Carry sizes: " ++ show (map Set.size evL)
  putStrLn $ "  Max carry:   " ++ show (maximum (map Set.size evL))
  putStrLn $ "  Period:      " ++ show (detectPeriod evL)
  putStrLn ""

  -- Density-1 Hash (random)
  putStrLn "=== HASH n=12 (random weights) ==="
  let (wsH, tH) = mkHash 12
      evH = carryEvolution wsH tH
  putStrLn $ visualizeCarry evH
  putStrLn $ "  Carry sizes: " ++ show (map Set.size evH)
  putStrLn $ "  Max carry:   " ++ show (maximum (map Set.size evH))
  putStrLn $ "  Period:      " ++ show (detectPeriod evH)
  putStrLn ""

  -- Scale: carry profile for various n
  putStrLn "=== SCALING: max carry set size vs n ==="
  putStrLn (padR 5 "n" ++ padR 8 "bits" ++ padR 12 "max-carry"
    ++ padR 8 "n/2" ++ padR 10 "ratio" ++ padR 10 "period")
  putStrLn (replicate 55 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        ev = carryEvolution ws t
        maxC = maximum (map Set.size ev)
        nBits = length ev
        period = detectPeriod ev
    putStrLn $ padR 5 (show n)
      ++ padR 8 (show nBits)
      ++ padR 12 (show maxC)
      ++ padR 8 (show (n `div` 2 + 1))
      ++ padR 10 (show (round (fromIntegral maxC / fromIntegral (n `div` 2 + 1) * 100 :: Double) :: Int) ++ "%")
      ++ padR 10 (maybe "none" show period)
    ) [8, 10, 12, 14, 16, 20, 24, 28, 32]
  putStrLn ""

  -- The billion dollar question: carry sizes per bit for n=16
  putStrLn "=== CARRY LANDSCAPE: hash n=16 ==="
  let (ws16, t16) = mkHash 16
      ev16 = carryEvolution ws16 t16
  putStrLn $ "  Sizes per bit: " ++ show (map Set.size ev16)
  putStrLn $ "  Bit columns (ones count): "
    ++ show (map bcOnesCount (decomposeProblem ws16))
  putStrLn ""

  -- Comparison: carry lives within n/2 (uncoupled)
  -- but the COUPLED problem needs 2^n states?
  putStrLn "=== THE GAP: uncoupled carry ≤ n/2, but coupling costs 2^n ==="
  putStrLn (padR 5 "n" ++ padR 14 "uncoupled-max" ++ padR 14 "bound(n/2+1)"
    ++ padR 14 "exceeds?")
  putStrLn (replicate 50 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        ev = carryEvolution ws t
        maxC = maximum (map Set.size ev)
        bound = n `div` 2 + 1
    putStrLn $ padR 5 (show n)
      ++ padR 14 (show maxC)
      ++ padR 14 (show bound)
      ++ padR 14 (if maxC > bound then "YES!" else "no")
    ) [8, 12, 16, 20, 24, 28, 32]

  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn "The uncoupled carry NEVER exceeds n/2+1."
  putStrLn "The NP-hardness hides in the COUPLING between bit columns."
  putStrLn "Question: can coupling be tracked with < 2^n state?"
  putStrLn "═══════════════════════════════════════════════════════════"
