module PeqNP.Landscape
  ( ProbLandscape(..)
  , buildLandscape
  , showLandscape
  , showHistogram
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import PeqNP.Relaxation (RelaxedSolution(..), solveRelaxed)
import PeqNP.Rounding (Seed, roundRandom)

-- | The probabilistic landscape of a Subset Sum instance.
--
-- By sampling N random roundings from the LP relaxation,
-- we build a histogram of achieved sums. The probability
-- of hitting the target determines the expected number of
-- trials needed by the randomized solver.
--
-- THE KEY METRIC: expectedTrials = 1 / targetProb
-- If this is polynomial in n → Subset Sum ∈ BPP → likely P = NP
-- If exponential → randomized rounding doesn't help
data ProbLandscape = PL
  { plElements       :: [Int]
  , plTarget         :: Int
  , plFractions      :: [Double]
  , plSamples        :: Int
  , plSumDistrib     :: Map Int Int  -- sum → frequency
  , plTargetHits     :: Int          -- how many times we hit the target
  , plTargetProb     :: Double       -- estimated P(hit target)
  , plExpectedTrials :: Double       -- 1/targetProb (Inf if 0)
  } deriving (Show)

-- | Build landscape by sampling N random roundings
buildLandscape :: Int -> [Int] -> Int -> ProbLandscape
buildLandscape nSamples elems target =
  let rs = solveRelaxed elems target
      fracs = rsFractions rs
      distrib = sampleAll nSamples fracs elems (42 :: Seed)
      hits = Map.findWithDefault 0 target distrib
      prob = fromIntegral hits / fromIntegral nSamples
  in PL
    { plElements       = elems
    , plTarget         = target
    , plFractions      = fracs
    , plSamples        = nSamples
    , plSumDistrib     = distrib
    , plTargetHits     = hits
    , plTargetProb     = prob
    , plExpectedTrials = if prob > 0 then 1.0 / prob else 1.0 / 0.0
    }
  where
    sampleAll :: Int -> [Double] -> [Int] -> Seed -> Map Int Int
    sampleAll 0 _ _ _ = Map.empty
    sampleAll n fracs ws seed =
      let (bits, seed') = roundRandom seed fracs
          s = sum [w | (w, True) <- zip ws bits]
          rest = sampleAll (n-1) fracs ws seed'
      in Map.insertWith (+) s 1 rest

-- | Pretty-print landscape summary
showLandscape :: ProbLandscape -> String
showLandscape pl = unlines
  [ "  Elements: " ++ show (plElements pl)
  , "  Target: " ++ show (plTarget pl)
  , "  Samples: " ++ show (plSamples pl)
  , "  Target hits: " ++ show (plTargetHits pl) ++ " / " ++ show (plSamples pl)
  , "  P(hit): " ++ show (roundTo 6 (plTargetProb pl))
  , "  Expected trials: " ++ (if isInfinite (plExpectedTrials pl) then "Inf (NO instance)"
                              else show (round (plExpectedTrials pl) :: Int))
  , "  Distinct sums hit: " ++ show (Map.size (plSumDistrib pl))
  ]

-- | ASCII histogram of sum distribution
showHistogram :: ProbLandscape -> String
showHistogram pl =
  let distrib = plSumDistrib pl
      maxFreq = if Map.null distrib then 1 else maximum (Map.elems distrib)
      target = plTarget pl
      entries = Map.toAscList distrib
      barWidth = 30
  in unlines
    [ "  " ++ padR 6 (show s)
      ++ (if s == target then ">" else "|")
      ++ replicate (freq * barWidth `div` max 1 maxFreq) '#'
      ++ " (" ++ show freq ++ ")"
    | (s, freq) <- entries
    ]

padR :: Int -> String -> String
padR n s = s ++ replicate (max 0 (n - length s)) ' '

roundTo :: Int -> Double -> Double
roundTo n x = fromIntegral (round (x * 10^n) :: Int) / 10^n
