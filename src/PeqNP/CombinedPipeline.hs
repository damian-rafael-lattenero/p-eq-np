module PeqNP.CombinedPipeline
  ( PipelineResult(..)
  , pipeline
  , showPipelineResult
    -- * Scaling
  , PipelineScaling(..)
  , pipelineScaling
  , showPipelineScaling
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Bits ((.&.))
import Data.List (sortBy)
import Data.Ord (comparing)

import PeqNP.DPSolver (dpReachable)
import PeqNP.BitDecompose (overlapForMultiplier)

-- | The combined pipeline: Kuperberg sieve → GF(2) analysis → solve.
--
-- 1. Kuperberg stage: pair weights matching on low √B bits, take differences
--    Reduces n → n' ≈ n/3, bits → bits' ≈ bits/2
-- 2. Measure overlap on reduced instance
-- 3. Solve reduced instance with brute force (it's small after sieve)
-- 4. Reconstruct: track pairing history to map solution back to original
--
-- THE KEY: pairing history is O(n) per stage — just record which pairs.
-- Reconstruction from a reduced solution is O(n): for each pair (i,j)
-- that produced difference d, if d is "included" in reduced solution,
-- then EITHER w_i is included and w_j isn't, OR vice versa.

data PairingRecord = PR
  { prLeftIdx   :: Int   -- index of first weight in original
  , prRightIdx  :: Int   -- index of second weight in original
  , prLeftVal   :: Int   -- original weight value
  , prRightVal  :: Int   -- original weight value
  , prDiff      :: Int   -- |leftVal - rightVal|
  , prShifted   :: Int   -- diff >> bitsMatched
  } deriving (Show)

data PipelineResult = PipeResult
  { prOrigWeights   :: [Int]
  , prOrigTarget    :: Int
  , prOrigN         :: Int
  , prOrigBits      :: Int
  , prOrigDP        :: Int
  , prOrigOverlap   :: Int
  -- After sieve
  , prReducedWeights :: [Int]
  , prReducedN      :: Int
  , prReducedBits   :: Int
  , prReducedDP     :: Int
  , prReducedOverlap :: Int
  , prPairings      :: [PairingRecord]
  , prUnpaired      :: [(Int, Int)]  -- (origIndex, value) of unpaired weights
  , prBitsMatched   :: Int
  -- Solution
  , prFound         :: Bool
  , prCorrect       :: Bool   -- agrees with DP on original?
  , prReducedSol    :: Maybe [Int]  -- solution subset of reduced weights
  , prOrigSol       :: Maybe [Int]  -- reconstructed solution on original
  -- Complexity
  , prSieveWork     :: Int    -- O(n)
  , prSolveWork     :: Int    -- 2^n' (brute force on reduced)
  , prTotalWork     :: Int
  , prDPWork        :: Int    -- DP on original (for comparison)
  , prSpeedup       :: Double
  } deriving (Show)

pipeline :: [Int] -> Int -> PipelineResult
pipeline elems target =
  let n = length elems
      maxW = maximum elems
      origBits = ceiling (logBase 2 (fromIntegral maxW + 1) :: Double)
      origDP = Set.size (dpReachable elems)
      origOverlap = overlapForMultiplier elems 1
      origHasSol = Set.member target (dpReachable elems)

      -- SIEVE STAGE: match √B low bits
      bitsToMatch = max 1 (floor (sqrt (fromIntegral origBits) :: Double))
      mask = (2 ^ bitsToMatch) - 1

      -- Group indexed weights by low bits
      indexed = zip [0..] elems
      groups = Map.fromListWith (++) [(w .&. mask, [(i, w)]) | (i, w) <- indexed]

      -- Pair up within each group, record history
      (pairings, unpairedList) = pairGroups (Map.toList groups) bitsToMatch

      -- Reduced weights = shifted differences
      reducedWeights = [prShifted p | p <- pairings, prShifted p > 0]
      -- Include unpaired weights (shifted)
      unpairedShifted = [(i, w `div` (2 ^ bitsToMatch)) | (i, w) <- unpairedList, w `div` (2 ^ bitsToMatch) > 0]
      allReduced = reducedWeights ++ map snd unpairedShifted

      reducedN = length allReduced
      reducedBits = if null allReduced then 0
                    else ceiling (logBase 2 (fromIntegral (maximum allReduced) + 1) :: Double)
      reducedDP = Set.size (dpReachable allReduced)
      reducedOverlap = if null allReduced then 0 else overlapForMultiplier allReduced 1

      -- SOLVE reduced instance by brute force (it's small!)
      reducedTarget = target `div` (2 ^ bitsToMatch)  -- approximate; see below
      allSubsets = generateSubsets allReduced
      reducedSolutions = [s | s <- allSubsets, sum s == reducedTarget]

      -- RECONSTRUCT solution on original (simplified: just verify with DP)
      found = not (null reducedSolutions)

      -- Complexity
      sieveWork = n
      solveWork = 2 ^ reducedN
      totalWork = sieveWork + solveWork

  in PipeResult
    { prOrigWeights    = elems
    , prOrigTarget     = target
    , prOrigN          = n
    , prOrigBits       = origBits
    , prOrigDP         = origDP
    , prOrigOverlap    = origOverlap
    , prReducedWeights = allReduced
    , prReducedN       = reducedN
    , prReducedBits    = reducedBits
    , prReducedDP      = reducedDP
    , prReducedOverlap = reducedOverlap
    , prPairings       = pairings
    , prUnpaired       = unpairedList
    , prBitsMatched    = bitsToMatch
    , prFound          = found
    , prCorrect        = found == origHasSol  -- NOTE: approximate, see caveat
    , prReducedSol     = if null reducedSolutions then Nothing else Just (head reducedSolutions)
    , prOrigSol        = Nothing  -- full reconstruction TODO
    , prSieveWork      = sieveWork
    , prSolveWork      = solveWork
    , prTotalWork      = totalWork
    , prDPWork         = origDP
    , prSpeedup        = fromIntegral origDP / fromIntegral (max 1 totalWork)
    }

pairGroups :: [(Int, [(Int, Int)])] -> Int -> ([PairingRecord], [(Int, Int)])
pairGroups [] _ = ([], [])
pairGroups ((_, items):rest) bitsMatched =
  let (pairs, leftover) = pairUp items bitsMatched
      (morePairs, moreLeftover) = pairGroups rest bitsMatched
  in (pairs ++ morePairs, leftover ++ moreLeftover)

pairUp :: [(Int, Int)] -> Int -> ([PairingRecord], [(Int, Int)])
pairUp [] _ = ([], [])
pairUp [x] _ = ([], [x])
pairUp ((i1,w1):(i2,w2):rest) bitsMatched =
  let diff = abs (w1 - w2)
      shifted = diff `div` (2 ^ bitsMatched)
      record = PR i1 i2 w1 w2 diff shifted
      (morePairs, leftover) = pairUp rest bitsMatched
  in (record : morePairs, leftover)

generateSubsets :: [Int] -> [[Int]]
generateSubsets [] = [[]]
generateSubsets (x:xs) = let r = generateSubsets xs in r ++ map (x:) r

showPipelineResult :: PipelineResult -> String
showPipelineResult pr = unlines
  [ "  ORIGINAL:  n=" ++ show (prOrigN pr) ++ " bits=" ++ show (prOrigBits pr)
      ++ " DP=" ++ show (prOrigDP pr) ++ " overlap=" ++ show (prOrigOverlap pr)
  , "  SIEVE:     matched " ++ show (prBitsMatched pr) ++ " low bits, "
      ++ show (length (prPairings pr)) ++ " pairs, "
      ++ show (length (prUnpaired pr)) ++ " unpaired"
  , "  REDUCED:   n'=" ++ show (prReducedN pr) ++ " bits'=" ++ show (prReducedBits pr)
      ++ " DP'=" ++ show (prReducedDP pr) ++ " overlap'=" ++ show (prReducedOverlap pr)
  , "  SOLVE:     found=" ++ show (prFound pr) ++ " correct=" ++ show (prCorrect pr)
  , "  WORK:      sieve=" ++ show (prSieveWork pr) ++ " + solve=2^" ++ show (prReducedN pr)
      ++ "=" ++ show (prSolveWork pr) ++ " total=" ++ show (prTotalWork pr)
  , "  vs DP:     " ++ show (prDPWork pr) ++ " → speedup " ++ show (round (prSpeedup pr) :: Int) ++ "x"
  ]

-- ═══════════════════════════════════════════════════════════
-- Scaling analysis
-- ═══════════════════════════════════════════════════════════

data PipelineScaling = PS
  { psN           :: Int
  , psBits        :: Int
  , psReducedN    :: Int
  , psReducedBits :: Int
  , psDP          :: Int
  , psReducedDP   :: Int
  , psSolveWork   :: Int
  , psSpeedup     :: Double
  , psCorrect     :: Bool
  , psOverlapOrig :: Int
  , psOverlapReduced :: Int
  } deriving (Show)

pipelineScaling :: [([Int], Int)] -> [PipelineScaling]
pipelineScaling = map run
  where
    run (ws, t) =
      let pr = pipeline ws t
      in PS (prOrigN pr) (prOrigBits pr) (prReducedN pr) (prReducedBits pr)
            (prOrigDP pr) (prReducedDP pr) (prSolveWork pr) (prSpeedup pr)
            (prCorrect pr) (prOrigOverlap pr) (prReducedOverlap pr)

showPipelineScaling :: [PipelineScaling] -> String
showPipelineScaling results = unlines $
  [ "  " ++ padR 4 "n" ++ padR 5 "b" ++ padR 5 "n'" ++ padR 5 "b'"
    ++ padR 7 "DP" ++ padR 7 "DP'" ++ padR 7 "work" ++ padR 8 "speed"
    ++ padR 5 "ov" ++ padR 5 "ov'" ++ "ok?"
  , "  " ++ replicate 60 '-'
  ] ++
  [ "  " ++ padR 4 (show (psN r)) ++ padR 5 (show (psBits r))
    ++ padR 5 (show (psReducedN r)) ++ padR 5 (show (psReducedBits r))
    ++ padR 7 (show (psDP r)) ++ padR 7 (show (psReducedDP r))
    ++ padR 7 (show (psSolveWork r))
    ++ padR 8 (show (round (psSpeedup r) :: Int) ++ "x")
    ++ padR 5 (show (psOverlapOrig r)) ++ padR 5 (show (psOverlapReduced r))
    ++ (if psCorrect r then "✓" else "✗")
  | r <- results
  ]

padR :: Int -> String -> String
padR n s = s ++ replicate (max 0 (n - length s)) ' '
