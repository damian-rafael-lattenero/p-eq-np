module PeqNP.LazyTree
  ( PruneStats(..)
  , searchWithStats
  , showPruneStats
  ) where

import Data.IORef (IORef, newIORef, modifyIORef', readIORef)
import System.IO.Unsafe (unsafePerformIO)

-- | Lazy decision tree with branch-and-bound pruning.
--
-- The tree is defined lazily — Haskell only evaluates branches we force.
-- Pruning criterion: a branch with partial sum s and remaining elements
-- rest is dead if:  s > target  OR  s + sum(rest) < target
--
-- The "bubbling soda" idea: branches that can't reach target evaporate
-- without ever being materialized in memory.

data PruneStats = PS
  { psNodesExplored :: Int
  , psTotalNodes    :: Int    -- 2^n
  , psPruneRatio    :: Double -- explored / total
  , psSolution      :: Maybe [Int]
  } deriving (Show)

-- | Search with branch-and-bound pruning, tracking how many nodes explored.
searchWithStats :: [Int] -> Int -> PruneStats
searchWithStats elems target =
  let totalNodes = (2 :: Int) ^ length elems
      counterRef = unsafePerformIO (newIORef (0 :: Int))
      solution = go counterRef 0 [] elems (sum elems)
      explored = unsafePerformIO (readIORef counterRef)
  in PS
    { psNodesExplored = explored
    , psTotalNodes    = totalNodes
    , psPruneRatio    = fromIntegral explored / fromIntegral (max 1 totalNodes)
    , psSolution      = solution
    }
  where
    go :: IORef Int -> Int -> [Int] -> [Int] -> Int -> Maybe [Int]
    go counter partialSum included [] _restSum =
      unsafePerformIO $ do
        modifyIORef' counter (+1)
        return $ if partialSum == target then Just (reverse included) else Nothing
    go counter partialSum included (x:xs) restSum
      -- Prune: partialSum already exceeds target
      | partialSum > target = Nothing
      -- Prune: even including everything remaining can't reach target
      | partialSum + restSum < target = Nothing
      | otherwise =
          unsafePerformIO $ do
            modifyIORef' counter (+1)
            let restSum' = restSum - x
                -- Try including x first (more likely to reach target)
                incResult = go counter (partialSum + x) (x : included) xs restSum'
            return $ case incResult of
              Just sol -> Just sol
              Nothing  -> go counter partialSum included xs restSum'

showPruneStats :: PruneStats -> String
showPruneStats ps = unlines
  [ "  Nodes explored: " ++ show (psNodesExplored ps)
      ++ " / " ++ show (psTotalNodes ps)
  , "  Prune ratio:    " ++ show (roundTo 4 (psPruneRatio ps))
      ++ (if psPruneRatio ps < 0.1 then " (excellent pruning!)"
          else if psPruneRatio ps < 0.5 then " (good pruning)"
          else " (poor pruning)")
  , "  Solution:       " ++ show (psSolution ps)
  ]
  where
    roundTo n x = fromIntegral (round (x * 10^n) :: Int) / 10^(n :: Int)
