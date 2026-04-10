module Main where

import PeqNP.BottomUpMITM
import PeqNP.ActorSolver (padR)
import qualified Data.IntSet as IS
import Data.Bits (xor, shiftR)
import Data.List (foldl')

-- ═══════════════════════════════════════════════════════════
-- Weight generators with controlled structure
-- ═══════════════════════════════════════════════════════════

-- | Pure LCG: strong arithmetic structure mod any prime.
mkLCG :: Int -> ([Int], Int)
mkLCG n =
  let ws = [2^n + ((i * 1103515245 + 12345) `mod` (2^(n-1))) | i <- [0..n-1]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

-- | Fully hashed: no exploitable structure.
mkHash :: Int -> ([Int], Int)
mkHash n =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
           | i <- [0..n-1]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

-- | Mixed: first k weights are LCG, rest are hashed.
-- k=n → pure LCG. k=0 → pure hash.
mkMixed :: Int -> Int -> ([Int], Int)
mkMixed n k =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      lcgPart  = [2^n + ((i * 1103515245 + 12345) `mod` (2^(n-1))) | i <- [0..k-1]]
      hashPart = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
                 | i <- [k..n-1]]
      ws = lcgPart ++ hashPart
      t  = sum ws `div` 2 + 1
  in (ws, t)

-- | Arithmetic progression: maximum structure.
mkAP :: Int -> ([Int], Int)
mkAP n =
  let ws = [2^n + i * 7 | i <- [0..n-1]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

-- ═══════════════════════════════════════════════════════════
-- Oracle fill rate measurement
-- ═══════════════════════════════════════════════════════════

-- | Compute the fill rate of the reachable set mod p for given weights.
-- Returns (reachable count, p, fill percentage).
oracleFillRate :: [Int] -> Int -> (Int, Int, Double)
oracleFillRate weights p =
  let reachable = foldl' (\acc w ->
        let wModP = w `mod` p
            shifted = IS.fromList [(r + wModP) `mod` p | r <- IS.toList acc]
        in IS.union acc shifted
        ) (IS.singleton 0) weights
      count = IS.size reachable
  in (count, p, 100 * fromIntegral count / fromIntegral p)

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " STRUCTURE vs RANDOMNESS: the phase transition"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Part 1: Fixed n=24, vary structure from AP → LCG → mixed → hash
  let n1 = 24
  putStrLn $ "=== n=" ++ show n1 ++ ": structure spectrum ==="
  putStrLn (padR 20 "instance"
    ++ padR 12 "states" ++ padR 12 "fill@1021"
    ++ padR 12 "fill@65537" ++ padR 12 "states/n^2")
  putStrLn (replicate 70 '-')

  let runOne label ws t = do
        let mr = bottomUpSolveMemo 2 ws t
            (_, _, fill1021)  = oracleFillRate ws 1021
            (_, _, fill65537) = oracleFillRate ws 65537
            d = fromIntegral (mrDistinctStates mr) :: Double
            fn = fromIntegral n1 :: Double
        putStrLn $ padR 20 label
          ++ padR 12 (show (mrDistinctStates mr))
          ++ padR 12 (showF 1 fill1021 ++ "%")
          ++ padR 12 (showF 1 fill65537 ++ "%")
          ++ padR 12 (showF 2 (d / fn^(2::Int)))

  let (wsAP, tAP) = mkAP n1
  runOne "arith-prog" wsAP tAP

  let (wsLCG, tLCG) = mkLCG n1
  runOne "LCG (full)" wsLCG tLCG

  -- Gradually mix hash into LCG
  mapM_ (\k -> do
    let frac = n1 - k
        label = "mix " ++ show frac ++ "/" ++ show n1 ++ " hash"
        (ws, t) = mkMixed n1 k
    runOne label ws t
    ) [n1, n1*3`div`4, n1`div`2, n1`div`4, n1`div`8, 0]

  let (wsH, tH) = mkHash n1
  runOne "full hash" wsH tH
  putStrLn ""

  -- Part 2: Scale n for each structure level
  putStrLn "=== SCALING: distinct states vs n for each structure type ==="
  putStrLn (padR 5 "n"
    ++ padR 12 "AP" ++ padR 12 "LCG"
    ++ padR 12 "50/50-mix" ++ padR 12 "full-hash"
    ++ padR 12 "2^(n/2)")
  putStrLn (replicate 66 '-')
  mapM_ (\n -> do
    let statesOf (ws, t) = mrDistinctStates (bottomUpSolveMemo 2 ws t)
        sAP   = statesOf (mkAP n)
        sLCG  = statesOf (mkLCG n)
        sMix  = statesOf (mkMixed n (n `div` 2))
        sHash = statesOf (mkHash n)
        half  = (2 :: Int) ^ (n `div` 2)
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show sAP)
      ++ padR 12 (show sLCG)
      ++ padR 12 (show sMix)
      ++ padR 12 (show sHash)
      ++ padR 12 (show half)
    ) [12, 16, 20, 24, 28, 32]
  putStrLn ""

  -- Part 3: Oracle fill rate vs n for hard instances
  putStrLn "=== ORACLE FILL RATE: hard instances, biggest prime (65537) ==="
  putStrLn (padR 5 "n" ++ padR 12 "reachable" ++ padR 12 "fill%" ++ padR 12 "states")
  putStrLn (replicate 44 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (cnt, _, pct) = oracleFillRate ws 65537
        mr = bottomUpSolveMemo 2 ws t
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show cnt)
      ++ padR 12 (showF 1 pct ++ "%")
      ++ padR 12 (show (mrDistinctStates mr))
    ) [10, 12, 14, 16, 18, 20, 24, 28, 32]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn "Key: when fill% → 100%, the oracle loses discriminating"
  putStrLn "power and distinct states explode exponentially."
  putStrLn "═══════════════════════════════════════════════════════════"

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int) / fromIntegral factor :: Double
  in show rounded
