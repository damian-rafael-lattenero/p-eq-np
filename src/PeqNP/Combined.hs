module PeqNP.Combined
  ( CombinedResult(..)
  , combinedSolve
  , showCombinedResult
  ) where

import qualified Data.Set as Set

import PeqNP.DPSolver (dpReachable)
import PeqNP.LLL (lllSolve, LLLResult(..), density)
import PeqNP.BitDecompose (overlapForMultiplier, gf2Rank, weightsToBitMatrix)
import PeqNP.Streaming (streamingSolve, StreamStats(..))
import PeqNP.Topological (gapPeriodicity, analyzeGaps, GapAnalysis(..))
import PeqNP.BitDecompose (overlapForMultiplier, gf2Rank, weightsToBitMatrix)

-- | Combined solver: try ALL methods, report which works.
-- This maps the "dead zone" — instances where nothing polynomial works.
data CombinedResult = CR
  { crElements    :: [Int]
  , crTarget      :: Int
  , crDensity     :: Double
  , crCorrectAns  :: Bool      -- from DP (ground truth)
  , crDPSize      :: Int       -- DP state space
  , crLLLWorks    :: Bool      -- LLL gives correct answer?
  , crStreamPeak  :: Int       -- streaming solver peak
  , crGF2Overlap  :: Int       -- bit overlap
  , crGF2Rank     :: Int       -- GF(2) rank of bit matrix
  , crGapPeriod   :: Maybe Int -- gap periodicity
  , crMethod      :: String    -- which method solved it (or "DEAD ZONE")
  } deriving (Show)

combinedSolve :: [Int] -> Int -> CombinedResult
combinedSolve elems target =
  let d = density elems
      n = length elems
      reachable = dpReachable elems
      correctAns = Set.member target reachable
      dpSize = Set.size reachable
      lll = if n <= 8 then lllSolve elems target
            else LLLResult False False Nothing d 0
      stream = streamingSolve elems target
      overlap = overlapForMultiplier elems 1
      rank = gf2Rank (weightsToBitMatrix elems)
      gaps = analyzeGaps elems
      period = gaPeriod gaps

      -- Determine which method "wins"
      method
        | llrCorrect lll && d < 1.0 = "LLL (density < 1)"
        | overlap == 0              = "GF(2) interleaved (overlap=0)"
        | period /= Nothing         = "Gap periodicity (mod " ++ show period ++ ")"
        | stMaxLive stream <= n * n = "Streaming (peak ≤ n²)"
        | dpSize <= n * n           = "DP (pseudo-poly, small sums)"
        | otherwise                 = "DEAD ZONE"

  in CR
    { crElements   = elems
    , crTarget     = target
    , crDensity    = d
    , crCorrectAns = correctAns
    , crDPSize     = dpSize
    , crLLLWorks   = llrCorrect lll
    , crStreamPeak = stMaxLive stream
    , crGF2Overlap = overlap
    , crGF2Rank    = rank
    , crGapPeriod  = period
    , crMethod     = method
    }

showCombinedResult :: CombinedResult -> String
showCombinedResult cr =
  "  d=" ++ padR 5 (show (round' 1 (crDensity cr)))
  ++ " DP=" ++ padR 6 (show (crDPSize cr))
  ++ " LLL=" ++ padR 3 (if crLLLWorks cr then "✓" else "✗")
  ++ " strm=" ++ padR 5 (show (crStreamPeak cr))
  ++ " ovlp=" ++ padR 3 (show (crGF2Overlap cr))
  ++ " gap=" ++ padR 5 (maybe "-" show (crGapPeriod cr))
  ++ " → " ++ crMethod cr
  where
    padR n s = s ++ replicate (max 0 (n - length s)) ' '
    round' n x = fromIntegral (round (x * 10^(n::Int)) :: Int) / 10^(n::Int)
