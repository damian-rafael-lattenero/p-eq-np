module PeqNP.KuperbergSieve
  ( -- * Kuperberg-style sieve for Subset Sum
    SieveResult(..)
  , kuperbergSieve
  , showSieveResult
    -- * Single sieve stage
  , SieveStage(..)
  , sieveStage
    -- * Analysis
  , SieveScaling(..)
  , sieveScaling
  , showSieveScaling
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Bits ((.&.))
import Data.List (sortBy)
import Data.Ord (comparing)

-- | Kuperberg-style sieve for Subset Sum.
--
-- THE KEY INSIGHT (from Flaxman-Przydatek 2005, based on Kuperberg's quantum sieve):
-- Instead of transforming the REPRESENTATION (GF(2) column operations),
-- transform the INSTANCE by combining weights.
--
-- Stage k:
-- 1. Group current weight-pairs by their lowest b bits (b ≈ √(log n))
-- 2. Within each group, take DIFFERENCES: w_i - w_j
--    This zeros out the b lowest bits (they matched!)
-- 3. The differences have b fewer significant bits
-- 4. Repeat on the remaining bits
--
-- After √(log n) stages of zeroing √(log n) bits each:
-- total bits reduced ≈ √(log n) × √(log n) = log n bits → trivial!
--
-- CRITICAL: this changes the Subset Sum instance. A solution to the
-- transformed instance maps back to a solution of the original via
-- tracking which pairs were combined.

data SieveStage = SS
  { ssStageNum     :: Int
  , ssInputWeights :: [Int]
  , ssOutputWeights :: [Int]
  , ssBitsZeroed   :: Int       -- how many low bits were matched/zeroed
  , ssInputCount   :: Int
  , ssOutputCount  :: Int       -- roughly inputCount/2 (pairing)
  , ssMaxBits      :: Int       -- max bit-width of output weights
  , ssPairsFormed  :: Int
  } deriving (Show)

-- | Perform one sieve stage: pair weights matching on low b bits, take differences.
sieveStage :: Int -> Int -> [Int] -> SieveStage
sieveStage stageNum bitsToMatch weights =
  let mask = (1 `shiftL'` bitsToMatch) - 1  -- mask for low b bits
      -- Group weights by their low b bits
      groups :: Map Int [Int]
      groups = Map.fromListWith (++) [(w .&. mask, [w]) | w <- weights]
      -- Within each group, pair up and take differences
      -- Each pair (w_i, w_j) where w_i ≡ w_j (mod 2^b) gives |w_i - w_j| with low b bits = 0
      diffs = concatMap pairAndDiff (Map.elems groups)
      -- Shift right by bitsToMatch (remove the zeroed bits)
      shifted = map (`div` (1 `shiftL'` bitsToMatch)) (filter (> 0) diffs)
      maxBit = if null shifted then 0
               else ceiling (logBase 2 (fromIntegral (maximum shifted) + 1) :: Double)
  in SS
    { ssStageNum     = stageNum
    , ssInputWeights = weights
    , ssOutputWeights = shifted
    , ssBitsZeroed   = bitsToMatch
    , ssInputCount   = length weights
    , ssOutputCount  = length shifted
    , ssMaxBits      = maxBit
    , ssPairsFormed  = length diffs
    }

-- | Pair up elements and take absolute differences
pairAndDiff :: [Int] -> [Int]
pairAndDiff [] = []
pairAndDiff [_] = []  -- odd one out, discard
pairAndDiff (a:b:rest) = abs (a - b) : pairAndDiff rest

shiftL' :: Int -> Int -> Int
shiftL' x n = x * (2 ^ n)

-- ═══════════════════════════════════════════════════════════
-- Full sieve: iterate stages until weights are small
-- ═══════════════════════════════════════════════════════════

data SieveResult = SR
  { srOriginalWeights :: [Int]
  , srOriginalTarget  :: Int
  , srStages          :: [SieveStage]
  , srFinalWeights    :: [Int]
  , srFinalBitWidth   :: Int
  , srTotalStages     :: Int
  , srSurvivingCount  :: Int
  , srOriginalBitWidth :: Int
  , srReductionRatio  :: Double  -- finalBitWidth / originalBitWidth
  } deriving (Show)

-- | Run the full Kuperberg sieve.
--
-- Strategy: at each stage, match √(currentBitWidth) low bits.
-- This gives O(√B) stages each reducing by √B bits → total O(B) bits reduced.
-- But we lose ~half the weights per stage (pairing).
-- Starting with n weights, after k stages: n/2^k weights remain.
-- After log(n) stages: 1 weight → trivial.
-- Bits per stage: B/√B = √B → after √B stages, all bits zeroed.
-- Total stages: min(√B, log n).
kuperbergSieve :: [Int] -> Int -> SieveResult
kuperbergSieve elems target =
  let maxW = if null elems then 1 else maximum elems
      origBits = ceiling (logBase 2 (fromIntegral maxW + 1) :: Double)
      stages = iterate' elems origBits 0 []
      finalWeights = if null stages then elems else ssOutputWeights (last stages)
      finalBits = if null stages then origBits
                  else ssMaxBits (last stages)
  in SR
    { srOriginalWeights  = elems
    , srOriginalTarget   = target
    , srStages           = stages
    , srFinalWeights     = finalWeights
    , srFinalBitWidth    = finalBits
    , srTotalStages      = length stages
    , srSurvivingCount   = length finalWeights
    , srOriginalBitWidth = origBits
    , srReductionRatio   = if origBits > 0
                           then fromIntegral finalBits / fromIntegral origBits
                           else 1.0
    }

iterate' :: [Int] -> Int -> Int -> [SieveStage] -> [SieveStage]
iterate' weights currentBits stageNum acc
  | length weights < 2 = acc  -- need at least 2 to pair
  | currentBits <= 1   = acc  -- bits already minimal
  | stageNum > 20      = acc  -- safety limit
  | otherwise =
      let -- Match √(currentBits) low bits per stage
          bitsToMatch = max 1 (floor (sqrt (fromIntegral currentBits) :: Double))
          stage = sieveStage stageNum bitsToMatch weights
          newWeights = ssOutputWeights stage
          newBits = ssMaxBits stage
      in if null newWeights || newBits >= currentBits
         then acc ++ [stage]  -- no progress, stop
         else iterate' newWeights newBits (stageNum + 1) (acc ++ [stage])

showSieveResult :: SieveResult -> String
showSieveResult sr = unlines $
  [ "  Original: " ++ show (length (srOriginalWeights sr)) ++ " weights, "
      ++ show (srOriginalBitWidth sr) ++ " bits"
  , "  Stages: " ++ show (srTotalStages sr)
  , "  Final: " ++ show (srSurvivingCount sr) ++ " weights, "
      ++ show (srFinalBitWidth sr) ++ " bits"
  , "  Bit reduction: " ++ show (srOriginalBitWidth sr) ++ " → " ++ show (srFinalBitWidth sr)
      ++ " (" ++ show (round' 1 (srReductionRatio sr * 100)) ++ "% remaining)"
  , "  Per stage:"
  ] ++
  [ "    Stage " ++ show (ssStageNum s) ++ ": "
      ++ show (ssInputCount s) ++ " → " ++ show (ssOutputCount s) ++ " weights, "
      ++ "zeroed " ++ show (ssBitsZeroed s) ++ " bits, "
      ++ "maxBits=" ++ show (ssMaxBits s)
  | s <- srStages sr
  ]
  where round' n x = fromIntegral (round (x * 10^(n::Int)) :: Int) / 10^(n::Int)

-- ═══════════════════════════════════════════════════════════
-- Scaling analysis: how does the sieve perform vs n?
-- ═══════════════════════════════════════════════════════════

data SieveScaling = SSc
  { sscN             :: Int
  , sscOrigBits      :: Int
  , sscFinalBits     :: Int
  , sscStages        :: Int
  , sscSurviving     :: Int
  , sscReduction     :: Double
  } deriving (Show)

sieveScaling :: [([Int], Int)] -> [SieveScaling]
sieveScaling instances =
  [ let sr = kuperbergSieve ws t
    in SSc (length ws) (srOriginalBitWidth sr) (srFinalBitWidth sr)
           (srTotalStages sr) (srSurvivingCount sr) (srReductionRatio sr)
  | (ws, t) <- instances
  ]

showSieveScaling :: [SieveScaling] -> String
showSieveScaling results = unlines $
  [ "  " ++ padR 4 "n" ++ padR 8 "origB" ++ padR 8 "finalB"
    ++ padR 8 "stages" ++ padR 8 "surv" ++ "reduction"
  , "  " ++ replicate 45 '-'
  ] ++
  [ "  " ++ padR 4 (show (sscN r))
    ++ padR 8 (show (sscOrigBits r))
    ++ padR 8 (show (sscFinalBits r))
    ++ padR 8 (show (sscStages r))
    ++ padR 8 (show (sscSurviving r))
    ++ show (round' 1 (sscReduction r * 100)) ++ "%"
  | r <- results
  ]
  where
    padR n s = s ++ replicate (max 0 (n - length s)) ' '
    round' n x = fromIntegral (round (x * 10^(n::Int)) :: Int) / 10^(n::Int)
