module PeqNP.Report
  ( showMonoidReport
  , showScalingTable
  ) where

import PeqNP.Search (MonoidReport(..), SearchResult(..))
import PeqNP.Impossibility (ScalingDataPoint(..))

-- | Pretty-print a monoid search report
showMonoidReport :: Show m => MonoidReport m -> String
showMonoidReport mr = unlines $
  [ "  Monoid: " ++ mrMonoidName mr ++ " (|M| = " ++ show (mrMonoidSize mr) ++ ")"
  , "  Instance has solution: " ++ show (mrHasSolution mr)
  , "  Any preserving homomorphism: " ++ show (mrAnyPreserve mr)
  , "  Generators:"
  ] ++
  [ "    " ++ padR 20 ("h(target)=" ++ show (srGenerator r))
    ++ " preserves: " ++ padR 6 (show (srPreserves r))
    ++ " collisions: " ++ padR 4 (show (srFalsePositives r))
    ++ " |image|: " ++ show (srImageSize r)
  | r <- mrResults mr
  ]

-- | Pretty-print scaling analysis as a table
showScalingTable :: [ScalingDataPoint] -> String
showScalingTable points = unlines $
  [ "  " ++ padR 4 "n" ++ padR 12 "target" ++ padR 12 "distinct" ++ padR 12 "min k"
  , "  " ++ replicate 40 '-'
  ] ++
  [ "  " ++ padR 4 (show (sdpN p))
    ++ padR 12 (show (sdpTarget p))
    ++ padR 12 (show (sdpDistinct p))
    ++ padR 12 (maybe "NOT FOUND" show (sdpMinK p))
  | p <- points
  ]

padR :: Int -> String -> String
padR n s = s ++ replicate (max 0 (n - length s)) ' '
