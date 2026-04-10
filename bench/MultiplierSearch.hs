module Main where

{-
  BASE CHANGE: reshape the decoherence wave

  In base 2: n bit positions, each reveals ~1 bit of subset identity.
  In base b: n/log(b) digit positions, each reveals ~log(b) bits.

  Same total information, different SHAPE.

  If we can concentrate decoherence at the BOTTOM (where pair checks
  handle it) and keep the TOP coherent → the tree stays small.

  Experiment: measure residue multiplicity in different bases.
  Residues mod b^{k+1} at digit position k.
-}

import qualified Data.Map.Strict as Map
import Data.Bits (xor, shiftR, testBit)
import PeqNP.ActorSolver (padR)

-- | Decoherence profile in base b.
-- At each digit position k: count distinct (sum mod b^{k+1}) values
-- among all 2^n subset sums.
-- Returns [(digit_position, distinct_residues, compression_ratio)]
decoherenceInBase :: Int -> [Int] -> [(Int, Int, Double)]
decoherenceInBase base weights =
  let n = length weights
      numSubsets = (2::Int)^n
      maxSum = sum weights
      numDigits = ceiling (logBase (fromIntegral base) (fromIntegral maxSum + 1) :: Double) + 1

      -- Precompute all subset sums
      allSums = [ subsetSum mask weights | mask <- [0..numSubsets-1] ]

  in [ let modulus = base ^ (k+1)
           residues = map (`mod` modulus) allSums
           counts = Map.fromListWith (+) [(r, 1::Int) | r <- residues]
           nd = Map.size counts
           compression = fromIntegral numSubsets / fromIntegral nd :: Double
       in (k, nd, compression)
     | k <- [0.. min numDigits 40]
     , base ^ (k+1) <= maxSum * 2  -- don't go beyond useful range
     ]
  where
    subsetSum mask ws = sum [w | (i,w) <- zip [0..] ws, testBit mask i]

-- | Carry set sizes in base b (uncoupled column processing).
-- At each digit position: how many possible carry values?
carryInBase :: Int -> [Int] -> [Int]
carryInBase base weights =
  let n = length weights
      maxSum = sum weights
      numDigits = ceiling (logBase (fromIntegral base) (fromIntegral maxSum + 1) :: Double) + 1
      targetDigits = toBaseDigits base (maxSum `div` 2 + 1) numDigits

      -- Column decomposition in base b
      columns = [ [digitAt base k w | w <- weights]
                | k <- [0..numDigits-1]
                ]

      -- Process columns: track carry set
      go [] carry = [length carry]
      go (col:cols) carry =
        let maxOnes = sum col  -- max contribution from this column
            targetDigit = if null targetDigits then 0
                          else targetDigits !! min (length targetDigits - 1) (numDigits - length cols - 1)
            carryOut = [ (c + selected) `div` base
                       | c <- carry
                       , selected <- [0..maxOnes]
                       , (c + selected) `mod` base == targetDigit
                       ]
        in length carry : go cols (unique carryOut)
  in go columns [0]

-- | Get digit k of number x in base b.
digitAt :: Int -> Int -> Int -> Int
digitAt base k x = (x `div` (base ^ k)) `mod` base

-- | Convert number to digits in base b (LSB first).
toBaseDigits :: Int -> Int -> Int -> [Int]
toBaseDigits base x numDigits =
  [digitAt base k x | k <- [0..numDigits-1]]

unique :: Eq a => [a] -> [a]
unique [] = []
unique (x:xs) = x : unique (filter (/= x) xs)

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
  putStrLn " BASE CHANGE: reshape the decoherence wave"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  let n = 14
      (ws, _t) = mkHash n
      numSubsets = (2::Int)^n
  putStrLn $ "Instance: HASH n=" ++ show n ++ ", 2^n=" ++ show numSubsets
  putStrLn ""

  -- Compare decoherence profiles across bases
  let bases = [(2, "base-2"), (3, "base-3"), (5, "base-5"),
               (n, "base-n"), (n*n, "base-n²")]

  mapM_ (\(b, label) -> do
    let profile = decoherenceInBase b ws
        carries = carryInBase b ws
    putStrLn $ "=== " ++ label ++ " (b=" ++ show b ++ ") ==="
    putStrLn (padR 8 "digit" ++ padR 14 "residues" ++ padR 14 "compress"
      ++ padR 14 "modulus")
    putStrLn (replicate 52 '-')
    mapM_ (\(k, nd, c) ->
      putStrLn $ padR 8 (show k)
        ++ padR 14 (show nd)
        ++ padR 14 (showF 1 c ++ ":1")
        ++ padR 14 (show (b ^ (k+1)))
      ) profile
    putStrLn $ "  Carry set sizes: " ++ show (take 20 carries)
    putStrLn $ "  Max carry set: " ++ show (maximum carries)
    putStrLn $ "  Digit positions: " ++ show (length profile)
    putStrLn ""
    ) bases

  -- Summary comparison: at what digit does compression drop below 2:1?
  putStrLn "=== SUMMARY: digits until compression < 2:1 ==="
  putStrLn (padR 10 "base" ++ padR 10 "digits" ++ padR 14 "total-compr"
    ++ padR 14 "carry-max" ++ padR 14 "decohere@50%")
  putStrLn (replicate 62 '-')
  mapM_ (\(b, label) -> do
    let profile = decoherenceInBase b ws
        carries = carryInBase b ws
        -- Find first digit where compression < 2:1
        halfPoint = case [(k,c) | (k, _, c) <- profile, c < 2.0] of
                      ((k,_):_) -> k
                      []        -> length profile
        -- Total compression at final digit
        totalCompr = case profile of
                       [] -> 1.0
                       _  -> let (_, _, c) = last profile in c
    putStrLn $ padR 10 label
      ++ padR 10 (show (length profile))
      ++ padR 14 (showF 1 totalCompr ++ ":1")
      ++ padR 14 (show (maximum carries))
      ++ padR 14 ("@digit " ++ show halfPoint)
    ) bases
  putStrLn ""

  -- THE KEY: normalized decoherence rate
  -- In each base, how much compression do we lose PER DIGIT?
  putStrLn "=== DECOHERENCE RATE: compression loss per digit ==="
  mapM_ (\(b, label) -> do
    let profile = decoherenceInBase b ws
        -- Rate = log(compression_first) / log(compression_last) / num_digits
        -- Or simpler: at each digit, ratio of compression to next
        rates = zipWith (\(_, _, c1) (_, _, c2) -> c1 / c2)
                  profile (tail profile)
        avgRate = if null rates then 1.0
                  else product rates ** (1.0 / fromIntegral (length rates))
    putStrLn $ "  " ++ padR 10 label
      ++ "avg decoherence/digit: " ++ showF 2 avgRate ++ "x"
      ++ "  over " ++ show (length profile) ++ " digits"
    ) bases
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn "If higher base has LOWER total decoherence → base matters!"
  putStrLn "If all bases reach 1:1 at the end → base is irrelevant."
  putStrLn "═══════════════════════════════════════════════════════════"

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int) / fromIntegral factor :: Double
  in show rounded
