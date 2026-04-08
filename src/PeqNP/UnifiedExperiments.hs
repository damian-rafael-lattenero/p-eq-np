module PeqNP.UnifiedExperiments
  ( UnifiedResult(..)
  , unifiedAnalysis
  , showUnifiedTable
  ) where

import qualified Data.Set as Set

import PeqNP.DPSolver (dpReachable)
import PeqNP.Impossibility (minDistinguishingModulus, MinSizeResult(..))
import PeqNP.PolyQuotient (minPreservingQ)
import PeqNP.Relaxation (solveRelaxed, RelaxedSolution(..))
import PeqNP.Streaming (streamingSolve, StreamStats(..))
import PeqNP.LazyTree (searchWithStats, PruneStats(..))
import PeqNP.FingerTree (fingerTreeSolve, FTStats(..))

-- | Unified result comparing ALL phases on one instance
data UnifiedResult = UR
  { urN              :: Int
  , urElements       :: [Int]
  , urTarget         :: Int
  , urHasSolution    :: Bool
  -- Phase A-C
  , urBruteForcePaths :: Int       -- 2^n
  , urDPSums         :: Int        -- distinct reachable sums
  -- Phase D
  , urMinModK        :: Maybe Int  -- min ZMod k
  -- Phase G
  , urMinPolyQ       :: Maybe Int  -- min poly quotient q
  -- Phase H
  , urLPConfidence   :: Double
  -- Phase I
  , urStreamPeak     :: Int        -- streaming max live
  , urLazyExplored   :: Int        -- lazy tree nodes explored
  , urFTExplored     :: Int        -- finger tree nodes explored
  , urFTPruned       :: Int        -- finger tree nodes pruned
  } deriving (Show)

-- | Run ALL analyses on a list of instances
unifiedAnalysis :: [([Int], Int)] -> [UnifiedResult]
unifiedAnalysis = map analyzeOne
  where
    analyzeOne (elems, target) =
      let n = length elems
          reachable = dpReachable elems
          dpSize = Set.size reachable
          hasSol = Set.member target reachable
          minK = msrMinModulus (minDistinguishingModulus elems target 200)
          minQ = minPreservingQ elems target 200
          lp = solveRelaxed elems target
          stream = streamingSolve elems target
          lazy = searchWithStats elems target
          ft = fingerTreeSolve elems target
      in UR
        { urN               = n
        , urElements        = elems
        , urTarget          = target
        , urHasSolution     = hasSol
        , urBruteForcePaths = (2 :: Int) ^ n
        , urDPSums          = dpSize
        , urMinModK         = minK
        , urMinPolyQ        = minQ
        , urLPConfidence    = rsConfidence lp
        , urStreamPeak      = stMaxLive stream
        , urLazyExplored    = psNodesExplored lazy
        , urFTExplored      = ftsExplored ft
        , urFTPruned        = ftsPruned ft
        }

showUnifiedTable :: [UnifiedResult] -> String
showUnifiedTable results = unlines $
  [ "  " ++ padR 4 "n"
    ++ padR 8 "2^n"
    ++ padR 8 "DP"
    ++ padR 8 "minK"
    ++ padR 8 "minQ"
    ++ padR 8 "LP cf"
    ++ padR 8 "strm"
    ++ padR 8 "lazy"
    ++ padR 8 "FT"
    ++ "ans"
  , "  " ++ replicate 72 '-'
  ] ++
  [ "  " ++ padR 4 (show (urN r))
    ++ padR 8 (show (urBruteForcePaths r))
    ++ padR 8 (show (urDPSums r))
    ++ padR 8 (maybe "-" show (urMinModK r))
    ++ padR 8 (maybe "-" show (urMinPolyQ r))
    ++ padR 8 (show (roundTo 2 (urLPConfidence r)))
    ++ padR 8 (show (urStreamPeak r))
    ++ padR 8 (show (urLazyExplored r))
    ++ padR 8 (show (urFTExplored r) ++ "/" ++ show (urFTPruned r))
    ++ (if urHasSolution r then "YES" else "NO")
  | r <- results
  ]

padR :: Int -> String -> String
padR n s = s ++ replicate (max 0 (n - length s)) ' '

roundTo :: Int -> Double -> Double
roundTo n x = fromIntegral (round (x * 10^(n :: Int)) :: Int) / 10^(n :: Int)
