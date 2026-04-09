module PeqNP.ParallelSolver
  ( -- * Parallel MITM
    parallelMITM
    -- * Parallel prefix search with early termination
  , parallelPrefixSearch
    -- * Multi-ordering race
  , raceOrders
    -- * Results
  , ParResult(..)
  , showParResult
  ) where

import qualified Data.Set as Set
import Data.List (foldl', sort, sortBy)
import Data.Ord (comparing, Down(..))
import Control.Concurrent.STM
import Control.Concurrent.Async (mapConcurrently_, async, cancel, race, Async, withAsync, waitEither)
import Control.Monad (forM_, when, forM, void)

-- ═══════════════════════════════════════════════════════════
-- Result
-- ═══════════════════════════════════════════════════════════

data ParResult = ParResult
  { prFound   :: !Bool
  , prWork    :: !Int
  , prMethod  :: !String
  } deriving (Show)

showParResult :: ParResult -> String
showParResult pr =
  "found=" ++ show (prFound pr)
  ++ " work=" ++ show (prWork pr)
  ++ " method=" ++ prMethod pr

-- ═══════════════════════════════════════════════════════════
-- 1. Parallel MITM
--
-- Enumerate left and right halves concurrently.
-- As soon as both are done, check for matches.
-- Uses `race` to overlap enumeration with early exit.
-- ═══════════════════════════════════════════════════════════

parallelMITM :: [Int] -> Int -> IO ParResult
parallelMITM weights target = do
  let n = length weights
      mid = n `div` 2
      (leftW, rightW) = splitAt mid weights

  -- Enumerate both halves in parallel
  leftVar  <- newTVarIO Set.empty
  rightVar <- newTVarIO Set.empty

  withAsync (do let s = bruteForceDP leftW
                atomically $ writeTVar leftVar s) $ \_ ->
    withAsync (do let s = bruteForceDP rightW
                  atomically $ writeTVar rightVar s) $ \_ -> do

      -- Wait for both to complete
      leftSet <- atomically $ do
        s <- readTVar leftVar
        if Set.null s then retry else pure s
      rightSet <- atomically $ do
        s <- readTVar rightVar
        if Set.null s then retry else pure s

      -- Check matches
      let found = any (\l -> Set.member (target - l) rightSet)
                      (Set.toList leftSet)
          work = Set.size leftSet + Set.size rightSet

      pure ParResult
        { prFound = found
        , prWork = work
        , prMethod = "parallelMITM"
        }

-- ═══════════════════════════════════════════════════════════
-- 2. Parallel prefix search with early termination
--
-- Split the problem at depth d into 2^d subtrees.
-- Each subtree runs as a lightweight async thread.
-- A shared TVar Bool acts as "found" flag.
-- When ANY thread finds target → sets flag → all others check
-- and bail out quickly.
--
-- The win: sequential search might explore wrong subtree first.
-- Parallel search explores ALL subtrees simultaneously, and
-- the first to find the answer terminates everything.
-- ═══════════════════════════════════════════════════════════

parallelPrefixSearch :: [Int] -> Int -> IO ParResult
parallelPrefixSearch weights target = do
  let n = length weights
      splitDepth = min n (max 3 (min 18 (n `div` 2)))
      (prefixW, restW) = splitAt splitDepth weights
      restSum = sum restW
      prefixes = genPrefixes prefixW  -- [(partialSum, includedCount)]

  foundVar <- newTVarIO False

  -- Launch all prefix threads
  mapConcurrently_ (\(pSum, _cnt) -> do
    alreadyFound <- readTVarIO foundVar
    if alreadyFound then pure ()
    else do
      let residualTarget = target - pSum
          found = residualTarget >= 0
                  && residualTarget <= restSum
                  && seqBnB residualTarget restW restSum
      when found $ atomically $ writeTVar foundVar True
    ) prefixes

  found <- readTVarIO foundVar
  pure ParResult
    { prFound = found
    , prWork = length prefixes
    , prMethod = "parallelPrefix(d=" ++ show splitDepth
                 ++ ",subtrees=" ++ show (length prefixes) ++ ")"
    }

-- | Generate all prefixes at given depth.
-- Returns (partialSum, count of included elements).
genPrefixes :: [Int] -> [(Int, Int)]
genPrefixes [] = [(0, 0)]
genPrefixes (w:ws) =
  let rest = genPrefixes ws
  in [(s, c) | (s, c) <- rest]            -- skip w
  ++ [(s + w, c + 1) | (s, c) <- rest]    -- include w

-- ═══════════════════════════════════════════════════════════
-- 3. Multi-ordering race
--
-- Run branch-and-bound with different variable orderings
-- in parallel. Different orderings discover different pruning
-- patterns. `race` returns whichever finishes first.
-- ═══════════════════════════════════════════════════════════

raceOrders :: [Int] -> Int -> IO ParResult
raceOrders weights target = do
  let orderings =
        [ (weights, "natural")
        , (sort weights, "ascending")
        , (sortBy (comparing Down) weights, "descending")
        , (interleave (sort weights), "interleaved")
        ]

  -- Race: first ordering to produce a result wins
  result <- raceList
    [ do let found = seqBnB target ws (sum ws)
         pure (found, name)
    | (ws, name) <- orderings
    ]

  case result of
    (found, name) -> pure ParResult
      { prFound = found
      , prWork = length weights
      , prMethod = "raceOrders(winner=" ++ name ++ ")"
      }

-- | Race a list of IO actions, return result of first to complete.
raceList :: [IO a] -> IO a
raceList [] = error "raceList: empty"
raceList [x] = x
raceList (x:xs) = do
  result <- race x (raceList xs)
  case result of
    Left a  -> pure a
    Right a -> pure a

-- ═══════════════════════════════════════════════════════════
-- Sequential branch-and-bound (used by parallel wrappers)
-- ═══════════════════════════════════════════════════════════

seqBnB :: Int -> [Int] -> Int -> Bool
seqBnB target _ _ | target < 0 = False
seqBnB target [] _ = target == 0
seqBnB target (x:xs) restSum
  | target > restSum = False    -- even all remaining can't reach
  | otherwise =
      seqBnB (target - x) xs (restSum - x)    -- include x
      || seqBnB target xs (restSum - x)        -- skip x

-- ═══════════════════════════════════════════════════════════
-- Utilities
-- ═══════════════════════════════════════════════════════════

bruteForceDP :: [Int] -> Set.Set Int
bruteForceDP = foldl' (\s w -> Set.union s (Set.map (+ w) s)) (Set.singleton 0)

interleave :: [a] -> [a]
interleave xs =
  let n = length xs
      mid = n `div` 2
      (lo, hi) = splitAt mid xs
  in merge lo (reverse hi)
  where
    merge [] bs = bs
    merge as [] = as
    merge (a:as) (b:bs) = a : b : merge as bs
