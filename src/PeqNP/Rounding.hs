module PeqNP.Rounding
  ( -- * PRNG
    Seed
  , nextRand
  , randDouble
    -- * Rounding strategies
  , roundRandom
  , roundThreshold
  , roundGreedy
    -- * Solver
  , checkRounding
  , tryNRoundings
  , SearchStats(..)
  , probabilisticSolve
  , showStats
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import PeqNP.Relaxation (RelaxedSolution(..), solveRelaxed)

-- ═══════════════════════════════════════════════════════════
-- Simple deterministic PRNG (LCG, no external deps)
-- ═══════════════════════════════════════════════════════════

type Seed = Int

-- | Linear congruential generator
nextRand :: Seed -> (Int, Seed)
nextRand s = let s' = (s * 1103515245 + 12345) `mod` (2^(31 :: Int))
             in (s' `mod` 10000, s')

-- | Random Double in [0, 1)
randDouble :: Seed -> (Double, Seed)
randDouble s = let (r, s') = nextRand s
               in (fromIntegral r / 10000.0, s')

-- ═══════════════════════════════════════════════════════════
-- Rounding strategies
-- ═══════════════════════════════════════════════════════════

-- | Random rounding: xᵢ → 1 with probability fᵢ
roundRandom :: Seed -> [Double] -> ([Bool], Seed)
roundRandom seed [] = ([], seed)
roundRandom seed (f:fs) =
  let (r, seed') = randDouble seed
      bit = r < f
      (rest, seed'') = roundRandom seed' fs
  in (bit : rest, seed'')

-- | Threshold rounding: xᵢ → 1 if fᵢ ≥ threshold
roundThreshold :: Double -> [Double] -> [Bool]
roundThreshold threshold = map (>= threshold)

-- | Greedy rounding: include in order of highest fraction until budget used
roundGreedy :: [Int] -> Int -> [Double] -> [Bool]
roundGreedy weights target fracs =
  let indexed = zip3 [0..] weights fracs
      sorted = reverse $ map (\(i,_,f) -> (i,f)) $ filter (\(_,_,f) -> f > 0)
               $ sortByFrac indexed
      result = go target sorted (replicate (length weights) False)
  in result
  where
    sortByFrac = id  -- already have fracs, just use them
    go _ [] bits = bits
    go remaining ((i,_):rest) bits
      | remaining <= 0 = bits
      | weights !! i <= remaining = go (remaining - weights !! i) rest (setAt i True bits)
      | otherwise = go remaining rest bits
    setAt _ _ [] = []
    setAt 0 v (_:xs) = v : xs
    setAt n v (x:xs) = x : setAt (n-1) v xs

-- ═══════════════════════════════════════════════════════════
-- Checking and solving
-- ═══════════════════════════════════════════════════════════

-- | Check if a rounding achieves the target sum
checkRounding :: [Int] -> Int -> [Bool] -> Bool
checkRounding weights target bits =
  sum [w | (w, True) <- zip weights bits] == target

-- | Try N random roundings, return the first that works
tryNRoundings :: Int -> [Int] -> Int -> [Double] -> Seed -> (Maybe [Int], Seed, Int)
tryNRoundings 0 _ _ _ seed = (Nothing, seed, 0)
tryNRoundings n weights target fracs seed =
  let (bits, seed') = roundRandom seed fracs
  in if checkRounding weights target bits
     then (Just [w | (w, True) <- zip weights bits], seed', n)
     else let (result, seed'', tried) = tryNRoundings (n-1) weights target fracs seed'
          in (result, seed'', tried)

-- ═══════════════════════════════════════════════════════════
-- Probabilistic solver with learning
-- ═══════════════════════════════════════════════════════════

data SearchStats = SS
  { ssAttempts     :: Int
  , ssCycles       :: Int
  , ssFound        :: Bool
  , ssSolution     :: Maybe [Int]
  , ssBestResidual :: Int
  , ssHitRate      :: Double     -- fraction of attempts that hit target
  , ssSumDistrib   :: Map Int Int -- sum → frequency
  } deriving (Show)

-- | Main probabilistic solver with restart cycles
probabilisticSolve :: Int -> Int -> [Int] -> Int -> SearchStats
probabilisticSolve attemptsPerCycle maxCycles weights target =
  go 0 0 maxInt Map.empty (42 :: Seed) -- initial seed
  where
    maxInt = maxBound :: Int
    rs = solveRelaxed weights target
    baseFracs = rsFractions rs

    go cycle totalAttempts bestRes distrib seed
      | cycle >= maxCycles = SS totalAttempts cycle False Nothing bestRes hitRate distrib
      | otherwise =
          let (result, seed', _tried) = tryBatch attemptsPerCycle baseFracs seed
          in case result of
            Just (sol, newDistrib, newBest) ->
              let distrib' = Map.unionWith (+) distrib newDistrib
              in SS (totalAttempts + attemptsPerCycle) (cycle+1) True (Just sol) newBest hitRate distrib'
            Nothing ->
              let (newDistrib, newBest) = sampleBatch attemptsPerCycle baseFracs seed
                  distrib' = Map.unionWith (+) distrib newDistrib
                  bestRes' = min bestRes newBest
              in go (cycle+1) (totalAttempts + attemptsPerCycle) bestRes' distrib' seed'
      where
        totalSoFar = if totalAttempts == 0 then 1 else totalAttempts
        hits = Map.findWithDefault 0 target distrib
        hitRate = fromIntegral hits / fromIntegral totalSoFar

    tryBatch 0 _ seed = (Nothing, seed, 0)
    tryBatch n fracs seed =
      let (bits, seed') = roundRandom seed fracs
          s = sum [w | (w, True) <- zip weights bits]
      in if s == target
         then (Just ([w | (w, True) <- zip weights bits], Map.singleton s 1, abs (s - target)), seed', n)
         else tryBatch (n-1) fracs seed'

    sampleBatch n fracs seed =
      let go' 0 distrib best _s = (distrib, best)
          go' k distrib best curSeed =
            let (bits, s') = roundRandom curSeed fracs
                achieved = sum [w | (w, True) <- zip weights bits]
                res = abs (achieved - target)
                distrib' = Map.insertWith (+) achieved 1 distrib
            in go' (k-1) distrib' (min best res) s'
      in go' n Map.empty maxInt seed

showStats :: SearchStats -> String
showStats ss = unlines
  [ "  Attempts: " ++ show (ssAttempts ss)
  , "  Cycles:   " ++ show (ssCycles ss)
  , "  Found:    " ++ show (ssFound ss)
  , "  Solution: " ++ show (ssSolution ss)
  , "  Best residual: " ++ show (ssBestResidual ss)
  , "  Hit rate: " ++ show (roundTo 6 (ssHitRate ss))
  ]
  where
    roundTo n x = fromIntegral (round (x * 10^(n :: Int)) :: Int) / 10^(n :: Int)
