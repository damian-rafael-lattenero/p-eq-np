module PeqNP.Relaxation
  ( RelaxedSolution(..)
  , solveRelaxed
  , showRelaxed
  ) where

import Data.List (sortBy)
import Data.Ord (comparing, Down(..))

-- | LP relaxation of Subset Sum.
--
-- Original: Σ wᵢxᵢ = T, xᵢ ∈ {0,1}
-- Relaxed:  Σ wᵢxᵢ = T, xᵢ ∈ [0,1]
--
-- The relaxed version is solvable in O(n log n) by greedy:
-- sort weights descending, greedily include until target reached,
-- last element gets a fractional value.
--
-- The fractional solution provides a "probability landscape" for
-- randomized rounding: elements with xᵢ ≈ 1 are very likely included,
-- elements with xᵢ ≈ 0 are very likely excluded.
data RelaxedSolution = RS
  { rsWeights    :: [Int]
  , rsTarget     :: Int
  , rsFractions  :: [Double]  -- ^ xᵢ ∈ [0,1] for each element (original order)
  , rsResidual   :: Double    -- ^ |Σ wᵢxᵢ - T|
  , rsConfidence :: Double    -- ^ How "integer-like": 1 - (Σ min(xᵢ, 1-xᵢ)) / n
  } deriving (Show)

-- | Solve the LP relaxation in O(n log n).
--
-- Algorithm: sort by weight descending, greedily fill.
-- If total sum < target, return all 1s with residual.
-- Otherwise, include largest elements fully, last one fractionally.
solveRelaxed :: [Int] -> Int -> RelaxedSolution
solveRelaxed elems target =
  let indexed = zip [0..] elems  -- (originalIndex, weight)
      sorted = sortBy (comparing (Down . snd)) indexed
      (fracs, _remaining) = fillGreedy (fromIntegral target) sorted
      -- Reconstruct in original order
      fracMap = zip (map fst sorted) fracs
      orderedFracs = [ lookupOr 0 i fracMap | i <- [0..length elems - 1] ]
      achieved = sum (zipWith (\w f -> fromIntegral w * f) elems orderedFracs)
      residual = abs (achieved - fromIntegral target)
      n = length elems
      conf = if n == 0 then 1.0
             else 1.0 - sum (map (\f -> min f (1.0 - f)) orderedFracs) / fromIntegral n
  in RS
    { rsWeights    = elems
    , rsTarget     = target
    , rsFractions  = orderedFracs
    , rsResidual   = residual
    , rsConfidence = conf
    }
  where
    fillGreedy :: Double -> [(Int, Int)] -> ([Double], Double)
    fillGreedy remaining [] = ([], remaining)
    fillGreedy remaining ((_, w):rest)
      | remaining <= 0 = (0 : map (const 0) rest, remaining)
      | fromIntegral w <= remaining =
          let (restFracs, r) = fillGreedy (remaining - fromIntegral w) rest
          in (1.0 : restFracs, r)
      | otherwise =
          let frac = remaining / fromIntegral w
              restFracs = map (const 0) rest
          in (frac : restFracs, 0)

    lookupOr :: Double -> Int -> [(Int, Double)] -> Double
    lookupOr def' i xs = case lookup i xs of
      Just v  -> v
      Nothing -> def'

-- | Pretty-print the relaxed solution
showRelaxed :: RelaxedSolution -> String
showRelaxed rs = unlines $
  [ "  Weights:    " ++ show (rsWeights rs)
  , "  Target:     " ++ show (rsTarget rs)
  , "  Fractions:  " ++ show (map (roundTo 3) (rsFractions rs))
  , "  Residual:   " ++ show (roundTo 6 (rsResidual rs))
  , "  Confidence: " ++ show (roundTo 3 (rsConfidence rs))
      ++ (if rsConfidence rs > 0.9 then " (high — easy to round)" else
          if rsConfidence rs > 0.5 then " (medium)" else " (low — hard to round)")
  ]

roundTo :: Int -> Double -> Double
roundTo n x = fromIntegral (round (x * 10^n) :: Int) / 10^n
