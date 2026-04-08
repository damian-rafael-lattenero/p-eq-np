module PeqNP.CategoryExperiments
  ( CategoryResult(..)
  , runAllConstructions
  , showComparisonTable
  ) where

import qualified Data.Set as Set

import PeqNP.DPSolver (dpReachable)
import PeqNP.ReachMonad (buildReachTree, totalDistinctStates)
import PeqNP.MyhillNerode (mnClassify, MNResult(..))
import PeqNP.VariableOrdering (naturalOrder, sortedAsc, sortedDesc, greedyMinStates, OrderingResult(..))
import PeqNP.Adjunction (buildMinimalIntermediate, intermediateSize)

-- | Result of one categorical construction on one instance
data CategoryResult = CR
  { crName :: String
  , crSize :: Int     -- size of the intermediate structure
  } deriving (Show)

-- | Run ALL categorical constructions on a single instance
runAllConstructions :: [Int] -> Int -> [CategoryResult]
runAllConstructions elems target =
  [ CR "DP reachable sums" (Set.size (dpReachable elems))
  , CR "Reach monad states" (if length elems <= 15 then totalDistinctStates (buildReachTree elems) else -1)
  , CR "MN classes (max)" (maximum (mnClassesPerLvl (mnClassify elems target)))
  , CR "MN sums (max)" (maximum (mnSumsPerLvl (mnClassify elems target)))
  , CR "Order: natural" (orMaxStates (naturalOrder elems))
  , CR "Order: sorted asc" (orMaxStates (sortedAsc elems))
  , CR "Order: sorted desc" (orMaxStates (sortedDesc elems))
  , CR "Order: greedy" (orMaxStates (greedyMinStates elems))
  , CR "Intermediate cat" (intermediateSize (buildMinimalIntermediate elems target))
  ]
  where
    mnClassesPerLvl = PeqNP.MyhillNerode.mnClassesPerLvl
    mnSumsPerLvl = PeqNP.MyhillNerode.mnSumsPerLvl

-- | Format comparison table
showComparisonTable :: [Int] -> Int -> String
showComparisonTable elems target =
  let results = runAllConstructions elems target
  in unlines $
    [ "  Instance: " ++ show elems ++ " target=" ++ show target
    , "  " ++ replicate 55 '-'
    ] ++
    [ "  " ++ padR 25 (crName r) ++ show (crSize r)
    | r <- results
    ]

padR :: Int -> String -> String
padR n s = s ++ replicate (max 0 (n - length s)) ' '
