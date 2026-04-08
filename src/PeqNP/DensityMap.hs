module PeqNP.DensityMap
  ( DensityResult(..)
  , testAtDensity
  , densitySweep
  , showDensitySweep
  ) where

import qualified Data.Set as Set

import PeqNP.DPSolver (dpReachable)
import PeqNP.LLL (lllSolve, LLLResult(..), density)
import PeqNP.Streaming (streamingSolve, StreamStats(..))
import PeqNP.BitDecompose (overlapForMultiplier)

-- | Result of testing one instance across multiple methods
data DensityResult = DR
  { drDensity   :: Double
  , drN         :: Int
  , drMaxWeight :: Int
  , drTarget    :: Int
  , drHasSol    :: Bool
  , drDPSize    :: Int       -- distinct reachable sums
  , drLLLFound  :: Bool      -- LLL found solution?
  , drLLLCorrect :: Bool     -- LLL correct?
  , drStreamPeak :: Int      -- streaming solver peak
  , drGF2Overlap :: Int      -- bit overlap
  } deriving (Show)

-- | Test a specific instance across all methods
testAtDensity :: [Int] -> Int -> DensityResult
testAtDensity elems target =
  let reachable = dpReachable elems
      hasSol = Set.member target reachable
      dpSize = Set.size reachable
      lll = lllSolve elems target
      stream = streamingSolve elems target
      overlap = overlapForMultiplier elems 1
  in DR
    { drDensity    = density elems
    , drN          = length elems
    , drMaxWeight  = if null elems then 0 else maximum elems
    , drTarget     = target
    , drHasSol     = hasSol
    , drDPSize     = dpSize
    , drLLLFound   = llrFound lll
    , drLLLCorrect = llrCorrect lll
    , drStreamPeak = stMaxLive stream
    , drGF2Overlap = overlap
    }

-- | Sweep across densities for fixed n
-- Generate instances by varying weight magnitude
densitySweep :: Int -> [DensityResult]
densitySweep n =
  [ let weights = generateWeights n maxW seed
        target = sum weights `div` 2 + 1  -- likely NO instance
    in testAtDensity weights target
  | (maxW, seed) <- [ (2^(n*4), 42)    -- very low density
                     , (2^(n*2), 43)    -- low density
                     , (2^n, 44)        -- density ≈ 1 (critical!)
                     , (2^(n `div` 2 + 2), 45) -- higher density
                     , (n * 10, 46)     -- high density
                     , (n * 3, 47)      -- very high density
                     ]
  ]

-- | Simple deterministic "random" weight generator
generateWeights :: Int -> Int -> Int -> [Int]
generateWeights n maxW seed =
  take n [1 + abs (lcg s) `mod` maxW | s <- iterate lcgNext seed]
  where
    lcg s = (s * 1103515245 + 12345) `mod` (2^(31 :: Int))
    lcgNext s = (s * 1103515245 + 12345) `mod` (2^(31 :: Int))

showDensitySweep :: [DensityResult] -> String
showDensitySweep results = unlines $
  [ "  " ++ padR 8 "density" ++ padR 6 "n" ++ padR 10 "maxW"
    ++ padR 8 "DP" ++ padR 6 "LLL" ++ padR 8 "strm" ++ padR 6 "ovlp" ++ "sol?"
  , "  " ++ replicate 58 '-'
  ] ++
  [ "  " ++ padR 8 (show (round' 2 (drDensity r)))
    ++ padR 6 (show (drN r))
    ++ padR 10 (show (drMaxWeight r))
    ++ padR 8 (show (drDPSize r))
    ++ padR 6 (if drLLLCorrect r then "✓" else "✗")
    ++ padR 8 (show (drStreamPeak r))
    ++ padR 6 (show (drGF2Overlap r))
    ++ (if drHasSol r then "YES" else "NO")
  | r <- results
  ]
  where
    padR n s = s ++ replicate (max 0 (n - length s)) ' '
    round' n x = fromIntegral (round (x * 10^(n::Int)) :: Int) / 10^(n::Int)
