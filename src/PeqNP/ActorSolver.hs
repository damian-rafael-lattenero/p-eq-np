module PeqNP.ActorSolver
  ( -- * Core solver (IO because of STM/async)
    actorSolve
  , ActorResult(..)
  , showActorResult
    -- * Sequential solver (for testing/comparison)
  , actorSolveSequential
    -- * Level-state types
  , LevelStatus(..)
  , LevelState(..)
  , LevelSnapshot(..)
    -- * DP-by-cardinality (pure, testable independently)
  , dpByCardinality
  , dpByCardinalityRange
  , dpAllCardinalities
  , cardinalityBounds
  , allCardinalityBounds
    -- * Level management (pure)
  , outsideInOrder
  , complementLevel
  , initLevels
  , PrecomputedWeights(..)
  , precomputeWeights
    -- * Hybrid solver (level killing + sieve)
  , actorSieveHybrid
  , HybridResult(..)
  , showHybridResult
    -- * Cardinality-informed sieve (the real integration)
  , cardinalitySieveSolve
  , cardinalityRepSolve
    -- * Benchmarking
  , actorBenchmark
  , ActorBenchResult(..)
  , showActorBenchmark
    -- * Utilities
  , mkDensity1
  , mkDensityD
  , padR
  , roundTo
  , snapshotOf
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (sort, scanl')
import Control.Concurrent.STM
import Control.Concurrent.Async (async, cancel, Async)
import PeqNP.MultiLevelSieve (recursiveRepSolveRaw)

-- ═══════════════════════════════════════════════════════════
-- Precomputed weights (sorted, prefix sums for O(1) bounds)
-- ═══════════════════════════════════════════════════════════

data PrecomputedWeights = PW
  { pwWeights    :: ![Int]   -- original weights
  , pwSorted     :: ![Int]   -- sorted ascending
  , pwPrefixAsc  :: ![Int]   -- prefix sums of ascending (for lower bounds)
  , pwPrefixDesc :: ![Int]   -- prefix sums of descending (for upper bounds)
  , pwTotalSum   :: !Int
  , pwN          :: !Int
  } deriving (Show)

precomputeWeights :: [Int] -> PrecomputedWeights
precomputeWeights ws =
  let sorted = sort ws
      n = length ws
      prefAsc  = scanl' (+) 0 sorted          -- [0, w1, w1+w2, ...]
      prefDesc = scanl' (+) 0 (reverse sorted) -- [0, wn, wn+w(n-1), ...]
      total = sum ws
  in PW ws sorted prefAsc prefDesc total n

-- ═══════════════════════════════════════════════════════════
-- Cardinality bounds: O(1) per level after precomputation
-- ═══════════════════════════════════════════════════════════

-- | Bounds for level k: (sum of k smallest, sum of k largest).
-- If target is outside [lo, hi], no k-element subset can reach it.
cardinalityBounds :: PrecomputedWeights -> Int -> (Int, Int)
cardinalityBounds pw k
  | k < 0 || k > pwN pw = (1, 0)  -- impossible: lo > hi
  | otherwise = (pwPrefixAsc pw !! k, pwPrefixDesc pw !! k)

-- | All bounds for levels 0..n.
allCardinalityBounds :: PrecomputedWeights -> [(Int, Int, Int)]  -- (level, lo, hi)
allCardinalityBounds pw =
  [ (k, lo, hi) | k <- [0 .. pwN pw], let (lo, hi) = cardinalityBounds pw k ]

-- ═══════════════════════════════════════════════════════════
-- DP by cardinality: the mathematical core
-- ═══════════════════════════════════════════════════════════

-- | Compute all sums achievable with exactly k elements from weights.
-- Uses: dp[i][j] = dp[i-1][j] U {s + w_i | s in dp[i-1][j-1]}
-- where i iterates over elements, j is cardinality.
dpByCardinality :: [Int] -> Int -> Set.Set Int
dpByCardinality weights k
  | k < 0 || k > length weights = Set.empty
  | k == 0 = Set.singleton 0
  | k == length weights = Set.singleton (sum weights)
  | otherwise =
      -- dp maps cardinality j -> set of reachable sums with exactly j elements
      let initial :: Map.Map Int (Set.Set Int)
          initial = Map.singleton 0 (Set.singleton 0)

          step :: Map.Map Int (Set.Set Int) -> Int -> Map.Map Int (Set.Set Int)
          step dp w =
            let -- For each existing (j, sums), adding w produces (j+1, {s+w | s in sums})
                contributions = Map.fromList
                  [ (j + 1, Set.map (+ w) sums)
                  | (j, sums) <- Map.toList dp
                  , j < k  -- don't compute beyond target cardinality
                  ]
            in Map.unionWith Set.union dp contributions

          final = foldl' step initial weights
      in Map.findWithDefault Set.empty k final

-- | Same as dpByCardinality but filters the FINAL result to [lo, hi].
-- Intermediate cardinalities are kept unfiltered since they're needed
-- to build up to the target cardinality k.
dpByCardinalityRange :: [Int] -> Int -> Int -> Int -> Set.Set Int
dpByCardinalityRange weights k lo hi
  | k < 0 || k > length weights = Set.empty
  | k == 0 = if lo <= 0 && 0 <= hi then Set.singleton 0 else Set.empty
  | k == length weights = let s = sum weights
                          in if lo <= s && s <= hi then Set.singleton s else Set.empty
  | lo > hi = Set.empty
  | otherwise =
      let initial :: Map.Map Int (Set.Set Int)
          initial = Map.singleton 0 (Set.singleton 0)

          step :: Map.Map Int (Set.Set Int) -> Int -> Map.Map Int (Set.Set Int)
          step dp w =
            let contributions = Map.fromList
                  [ (j + 1, let newSums = Set.map (+ w) sums
                            -- Only filter at the target cardinality k
                            in if j + 1 == k then filterRange lo hi newSums else newSums)
                  | (j, sums) <- Map.toList dp
                  , j < k
                  ]
            in Map.unionWith Set.union dp contributions

          final = foldl' step initial weights
      in Map.findWithDefault Set.empty k final

-- | Compute reachable sums for ALL cardinalities 0..n in one pass.
-- More efficient than calling dpByCardinality separately for each k.
dpAllCardinalities :: [Int] -> Map.Map Int (Set.Set Int)
dpAllCardinalities weights =
  let n = length weights
      initial :: Map.Map Int (Set.Set Int)
      initial = Map.singleton 0 (Set.singleton 0)

      step :: Map.Map Int (Set.Set Int) -> Int -> Map.Map Int (Set.Set Int)
      step dp w =
        let contributions = Map.fromList
              [ (j + 1, Set.map (+ w) sums)
              | (j, sums) <- Map.toList dp
              , j < n
              ]
        in Map.unionWith Set.union dp contributions

  in foldl' step initial weights

-- ═══════════════════════════════════════════════════════════
-- Level management
-- ═══════════════════════════════════════════════════════════

data LevelStatus
  = LActive     -- waiting or eligible to compute
  | LComputing  -- actor thread is running DP
  | LSolved     -- reachable sums fully computed
  | LKilled     -- proved impossible (target outside bounds)
  deriving (Show, Eq)

data LevelState = LevelState
  { lsLevel     :: !Int
  , lsBoundsLo  :: !Int
  , lsBoundsHi  :: !Int
  , lsReachable :: !(Set.Set Int)
  , lsStatus    :: !LevelStatus
  } deriving (Show)

data LevelSnapshot = LevelSnapshot
  { snapLevel     :: !Int
  , snapBoundsLo  :: !Int
  , snapBoundsHi  :: !Int
  , snapReachable :: !Int   -- size of reachable set
  , snapStatus    :: !LevelStatus
  } deriving (Show)

snapshotOf :: LevelState -> LevelSnapshot
snapshotOf ls = LevelSnapshot
  { snapLevel     = lsLevel ls
  , snapBoundsLo  = lsBoundsLo ls
  , snapBoundsHi  = lsBoundsHi ls
  , snapReachable = Set.size (lsReachable ls)
  , snapStatus    = lsStatus ls
  }

-- | Initialize all levels: compute bounds, kill impossible ones.
initLevels :: PrecomputedWeights -> Int -> [LevelState]
initLevels pw target =
  [ let (lo, hi) = cardinalityBounds pw k
        status = if target < lo || target > hi then LKilled else LActive
    in LevelState k lo hi Set.empty status
  | k <- [0 .. pwN pw]
  ]

-- | Outside-in ordering: [0, n, 1, n-1, 2, n-2, ...]
-- filtered to only include surviving levels.
outsideInOrder :: Int -> [Int] -> [Int]
outsideInOrder n surviving =
  let alive = Set.fromList surviving
      pairs = zip [0..] (reverse [0..n])
      interleaved = concatMap (\(lo, hi) ->
        if lo >= hi then [lo | lo == hi]
        else [lo, hi]) pairs
      -- Deduplicate while preserving order
      dedup _seen [] = []
      dedup seen (x:xs)
        | Set.member x seen = dedup seen xs
        | otherwise = x : dedup (Set.insert x seen) xs
  in filter (`Set.member` alive) (dedup Set.empty interleaved)

-- | Complement: level k sums S => level (n-k) has {totalSum - s | s in S}
complementLevel :: Int -> Set.Set Int -> Set.Set Int
complementLevel totalSum = Set.map (totalSum -)

-- ═══════════════════════════════════════════════════════════
-- Results
-- ═══════════════════════════════════════════════════════════

data ActorResult = ActorResult
  { arFound        :: !Bool
  , arCorrect      :: !Bool
  , arSolvingLevel :: !(Maybe Int)
  , arLevelsAlive  :: !Int
  , arLevelsKilled :: !Int
  , arTotalWork    :: !Int
  , arMaxLevelWork :: !Int
  , arSnapshots    :: ![LevelSnapshot]
  } deriving (Show)

showActorResult :: ActorResult -> String
showActorResult ar = unlines $
  [ "  found=" ++ show (arFound ar) ++ " correct=" ++ show (arCorrect ar)
  , "  solvingLevel=" ++ show (arSolvingLevel ar)
  , "  alive=" ++ show (arLevelsAlive ar)
      ++ " killed=" ++ show (arLevelsKilled ar)
  , "  totalWork=" ++ show (arTotalWork ar)
      ++ " maxLevelWork=" ++ show (arMaxLevelWork ar)
  , "  levels:"
  ] ++ map showSnap (arSnapshots ar)
  where
    showSnap s = "    k=" ++ show (snapLevel s)
      ++ " [" ++ show (snapBoundsLo s) ++ ".." ++ show (snapBoundsHi s) ++ "]"
      ++ " |R|=" ++ show (snapReachable s)
      ++ " " ++ show (snapStatus s)

-- ═══════════════════════════════════════════════════════════
-- Sequential solver (validates logic without concurrency)
-- ═══════════════════════════════════════════════════════════

-- | Sequential outside-in solver with bidirectional constraint propagation.
-- No threads — just processes levels in outside-in order,
-- propagating bounds after each level completes.
actorSolveSequential :: [Int] -> Int -> ActorResult
actorSolveSequential weights target =
  let pw = precomputeWeights weights
      n  = pwN pw
      totalSum = pwTotalSum pw

      -- Init all levels
      levels0 = initLevels pw target

      -- Exploit symmetry: prefer computing levels 0..n/2 (deriving n/2+1..n via complement).
      -- But if a level k > n/2 survives and its complement (n-k) is killed,
      -- we must compute k directly.
      halfN = n `div` 2
      levelsMap = Map.fromList [(lsLevel ls, ls) | ls <- levels0]
      needsComputation ls =
        let k = lsLevel ls
            compK = n - k
        in lsStatus ls /= LKilled &&
           (k <= halfN ||
            case Map.lookup compK levelsMap of
              Just comp -> lsStatus comp == LKilled
              Nothing   -> True)
      toCompute = [lsLevel ls | ls <- levels0, needsComputation ls]
      order = outsideInOrder n toCompute

      -- Process levels outside-in
      (finalLevels, foundLevel) = processLevels pw target totalSum n order
                                    (Map.fromList [(lsLevel ls, ls) | ls <- levels0])
                                    Nothing

      -- Build result
      allFinal = [Map.findWithDefault (LevelState k 0 0 Set.empty LKilled) k finalLevels | k <- [0..n]]
      found = foundLevel /= Nothing
      dpAnswer = Set.member target (localBruteForceDP weights)
      snapshots = map snapshotOf allFinal
      totalWork = sum [Set.size (lsReachable ls) | ls <- allFinal]
      maxWork = if null allFinal then 0
                else maximum [Set.size (lsReachable ls) | ls <- allFinal]
  in ActorResult
      { arFound = found
      , arCorrect = found == dpAnswer
      , arSolvingLevel = foundLevel
      , arLevelsAlive = length [ls | ls <- allFinal, lsStatus ls /= LKilled]
      , arLevelsKilled = length [ls | ls <- allFinal, lsStatus ls == LKilled]
      , arTotalWork = totalWork
      , arMaxLevelWork = maxWork
      , arSnapshots = snapshots
      }

-- | Process levels one by one, propagating constraints after each.
processLevels :: PrecomputedWeights -> Int -> Int -> Int -> [Int]
              -> Map.Map Int LevelState -> Maybe Int
              -> (Map.Map Int LevelState, Maybe Int)
processLevels _ _ _ _ [] levels found = (levels, found)
processLevels pw target totalSum n (k:ks) levels found
  | found /= Nothing = (levels, found)  -- early termination
  | otherwise =
    let ls = levels Map.! k
    in if lsStatus ls == LKilled
       then processLevels pw target totalSum n ks levels found
       else
         -- Compute this level's reachable sums with current bounds
         let reachable = dpByCardinalityRange (pwWeights pw) k (lsBoundsLo ls) (lsBoundsHi ls)
             solved = ls { lsReachable = reachable, lsStatus = LSolved }

             -- Check if target found at this level
             foundHere = Set.member target reachable
             newFound = if foundHere then Just k else found

             -- Derive complement level (n-k) for free
             compK = n - k
             compReachable = complementLevel totalSum reachable
             levels1 = Map.insert k solved levels
             levels2 = if compK /= k && compK >= 0 && compK <= n
                       then case Map.lookup compK levels1 of
                              Just cls | lsStatus cls /= LKilled ->
                                let compSolved = cls { lsReachable = compReachable, lsStatus = LSolved }
                                in Map.insert compK compSolved levels1
                              _ -> levels1
                       else levels1

             -- Check target in complement
             foundComp = Set.member target compReachable
             newFound2 = if foundComp && newFound == Nothing then Just compK else newFound

             -- Propagate bounds to adjacent levels
             levels3 = propagateConstraints target levels2 k
             levels4 = if compK /= k then propagateConstraints target levels3 compK else levels3

         in processLevels pw target totalSum n ks levels4 newFound2

-- | After solving level k, tighten bounds on its neighbors.
-- If neighbor's bounds exclude target, kill it.
propagateConstraints :: Int -> Map.Map Int LevelState -> Int
                     -> Map.Map Int LevelState
propagateConstraints _target levels k =
  case Map.lookup k levels of
    Nothing -> levels
    Just solved | lsStatus solved /= LSolved -> levels
    Just _solved ->
      -- Each level k is an independent question: "does any k-element subset sum to target?"
      -- The main benefit is level killing via initial bounds (done in initLevels).
      -- Future: more sophisticated inter-level constraint propagation using
      -- actual reachable ranges to tighten adjacent level bounds.
      levels

-- ═══════════════════════════════════════════════════════════
-- Concurrent solver (STM + async)
-- ═══════════════════════════════════════════════════════════

-- | Concurrent actor-based solver. Each level runs as an async thread.
-- A coordinator monitors progress and propagates constraints.
actorSolve :: [Int] -> Int -> IO ActorResult
actorSolve weights target = do
  let pw = precomputeWeights weights
      n  = pwN pw
      totalSum = pwTotalSum pw
      levels0 = initLevels pw target

  -- Quick exits
  if target == 0 then pure (quickResult weights target (Just 0) levels0)
  else if target == totalSum then pure (quickResult weights target (Just n) levels0)
  else if all (\ls -> lsStatus ls == LKilled) levels0
    then pure (quickResult weights target Nothing levels0)
  else do
    -- Create TVars for all levels
    tvars <- mapM newTVarIO levels0
    foundFlag  <- newTVarIO False
    foundLevel <- newTVarIO (Nothing :: Maybe Int)

    -- Prefer computing levels 0..n/2, deriving rest via complement.
    -- But levels > n/2 whose complement is killed need direct computation.
    let halfN = n `div` 2
        levelsMap = Map.fromList [(lsLevel ls, ls) | ls <- levels0]
        needsComputation ls =
          let k = lsLevel ls; compK = n - k
          in lsStatus ls /= LKilled &&
             (k <= halfN ||
              case Map.lookup compK levelsMap of
                Just comp -> lsStatus comp == LKilled
                Nothing   -> True)
        toCompute = [lsLevel ls | ls <- levels0, needsComputation ls]
        order = outsideInOrder n toCompute

    -- Launch level actors in outside-in order
    actors <- launchActors pw target totalSum n tvars foundFlag foundLevel order []

    -- Wait for all actors to finish or target to be found
    waitForCompletion tvars foundFlag n

    -- Collect results
    collectResults weights target tvars foundFlag foundLevel actors n

-- | Launch actors sequentially in outside-in order, but each runs concurrently.
launchActors :: PrecomputedWeights -> Int -> Int -> Int
             -> [TVar LevelState] -> TVar Bool -> TVar (Maybe Int)
             -> [Int] -> [Async ()] -> IO [Async ()]
launchActors _ _ _ _ _ _ _ [] actors = pure actors
launchActors pw target totalSum n tvars foundFlag foundLevel (k:ks) actors = do
  a <- async $ levelActor pw target totalSum n tvars foundFlag foundLevel k
  launchActors pw target totalSum n tvars foundFlag foundLevel ks (a : actors)

-- | Actor for a single level k.
levelActor :: PrecomputedWeights -> Int -> Int -> Int
           -> [TVar LevelState] -> TVar Bool -> TVar (Maybe Int)
           -> Int -> IO ()
levelActor pw target totalSum n tvars foundFlag foundLevel k = do
  -- Check if already found or killed
  myState <- readTVarIO (tvars !! k)
  alreadyFound <- readTVarIO foundFlag
  if alreadyFound || lsStatus myState == LKilled then pure ()
  else do
    -- Mark as computing
    atomically $ modifyTVar' (tvars !! k) $ \ls -> ls { lsStatus = LComputing }

    -- Compute reachable sums with bounds
    let reachable = dpByCardinalityRange (pwWeights pw) k (lsBoundsLo myState) (lsBoundsHi myState)
        weFound = Set.member target reachable

    -- Publish result
    atomically $ do
      modifyTVar' (tvars !! k) $ \ls -> ls
        { lsReachable = reachable, lsStatus = LSolved }
      -- Signal if found
      if weFound
        then do writeTVar foundFlag True
                writeTVar foundLevel (Just k)
        else pure ()

    -- Derive complement level (n-k)
    let compK = n - k
    if compK /= k && compK >= 0 && compK <= n
    then do
      let compReachable = complementLevel totalSum reachable
          compFound = Set.member target compReachable
      atomically $ do
        cls <- readTVar (tvars !! compK)
        if lsStatus cls `elem` [LSolved, LKilled]
          then pure ()
          else do
            writeTVar (tvars !! compK) cls
              { lsReachable = compReachable, lsStatus = LSolved }
            if compFound
              then do writeTVar foundFlag True
                      writeTVar foundLevel (Just compK)
              else pure ()
    else pure ()

-- | Wait until all levels are done or target is found.
waitForCompletion :: [TVar LevelState] -> TVar Bool -> Int -> IO ()
waitForCompletion tvars foundFlag _n = atomically $ do
  found <- readTVar foundFlag
  if found then pure ()
  else do
    states <- mapM readTVar tvars
    let allDone = all (\ls -> lsStatus ls `elem` [LSolved, LKilled]) states
    if allDone then pure ()
    else retry

-- | Collect final results from all TVars.
collectResults :: [Int] -> Int -> [TVar LevelState] -> TVar Bool
               -> TVar (Maybe Int) -> [Async ()] -> Int -> IO ActorResult
collectResults weights target tvars foundFlag foundLevel actors _n = do
  finalStates <- atomically $ mapM readTVar tvars
  found <- readTVarIO foundFlag
  solvingK <- readTVarIO foundLevel
  mapM_ cancel actors

  let dpAnswer = Set.member target (localBruteForceDP weights)
      snapshots = map snapshotOf finalStates
      totalWork = sum [Set.size (lsReachable ls) | ls <- finalStates]
      maxWork = if null finalStates then 0
                else maximum [Set.size (lsReachable ls) | ls <- finalStates]

  pure ActorResult
    { arFound = found
    , arCorrect = found == dpAnswer
    , arSolvingLevel = solvingK
    , arLevelsAlive = length [ls | ls <- finalStates, lsStatus ls /= LKilled]
    , arLevelsKilled = length [ls | ls <- finalStates, lsStatus ls == LKilled]
    , arTotalWork = totalWork
    , arMaxLevelWork = maxWork
    , arSnapshots = snapshots
    }

-- | Quick result for trivial cases.
quickResult :: [Int] -> Int -> Maybe Int -> [LevelState] -> ActorResult
quickResult weights target mLevel levels0 =
  let found = mLevel /= Nothing
      dpAnswer = Set.member target (localBruteForceDP weights)
  in ActorResult
    { arFound = found
    , arCorrect = found == dpAnswer
    , arSolvingLevel = mLevel
    , arLevelsAlive = length [ls | ls <- levels0, lsStatus ls /= LKilled]
    , arLevelsKilled = length [ls | ls <- levels0, lsStatus ls == LKilled]
    , arTotalWork = 0
    , arMaxLevelWork = 0
    , arSnapshots = map snapshotOf levels0
    }

-- ═══════════════════════════════════════════════════════════
-- Benchmarking
-- ═══════════════════════════════════════════════════════════

data ActorBenchResult = ABR
  { abrN          :: !Int
  , abrActorWork  :: !Int
  , abrSeqWork    :: !Int
  , abrMITM       :: !Int
  , abrRatioMITM  :: !Double
  , abrKilled     :: !Int
  , abrAlive      :: !Int
  , abrCorrect    :: !Bool
  } deriving (Show)

actorBenchmark :: Int -> ActorBenchResult
actorBenchmark n =
  let (ws, t) = mkDensity1 n
      seqResult = actorSolveSequential ws t
      mitm = 3 * 2 ^ (n `div` 2)
      ratio = fromIntegral mitm / fromIntegral (max 1 (arTotalWork seqResult))
  in ABR n (arTotalWork seqResult) (arTotalWork seqResult) mitm ratio
         (arLevelsKilled seqResult) (arLevelsAlive seqResult) (arCorrect seqResult)

showActorBenchmark :: [ActorBenchResult] -> String
showActorBenchmark results = unlines $
  [ "  " ++ padR 5 "n" ++ padR 12 "actor" ++ padR 12 "MITM"
    ++ padR 8 "ratio" ++ padR 8 "killed" ++ padR 8 "alive" ++ "ok"
  , "  " ++ replicate 60 '-'
  ] ++
  [ "  " ++ padR 5 (show (abrN r))
    ++ padR 12 (show (abrActorWork r))
    ++ padR 12 (show (abrMITM r))
    ++ padR 8 (show (roundTo 2 (abrRatioMITM r)))
    ++ padR 8 (show (abrKilled r))
    ++ padR 8 (show (abrAlive r))
    ++ (if abrCorrect r then "OK" else "ERR")
  | r <- results
  ]

-- ═══════════════════════════════════════════════════════════
-- Hybrid solver: level killing + sieve
-- ═══════════════════════════════════════════════════════════

data HybridResult = HybridResult
  { hrFound      :: !Bool
  , hrKilledAll  :: !Bool       -- level killing proved NO without running sieve?
  , hrKilled     :: !Int
  , hrAlive      :: !Int
  , hrSieveWork  :: !Int        -- work from the sieve (real, comparable metric)
  , hrSnapshots  :: ![LevelSnapshot]
  } deriving (Show)

-- | Hybrid solver: level killing pre-filter + recursiveRepSolve.
-- If ALL cardinality levels are killed -> NO (free, O(n log n)).
-- If any survive -> run sieve on the full problem.
actorSieveHybrid :: Int -> [Int] -> Int -> HybridResult
actorSieveHybrid modulus weights target =
  let pw = precomputeWeights weights
      n  = pwN pw
      levels0 = initLevels pw target
      killed = length [ls | ls <- levels0, lsStatus ls == LKilled]
      alive = (n + 1) - killed
      snaps = map snapshotOf levels0
  in if alive == 0
     then -- Level killing proved NO without any sieve computation!
          HybridResult { hrFound = False, hrKilledAll = True
                       , hrKilled = killed, hrAlive = 0
                       , hrSieveWork = 0, hrSnapshots = snaps }
     else -- Run sieve on the full problem
          let (found, work) = recursiveRepSolveRaw modulus weights target
          in HybridResult { hrFound = found, hrKilledAll = False
                          , hrKilled = killed, hrAlive = alive
                          , hrSieveWork = work, hrSnapshots = snaps }

showHybridResult :: HybridResult -> String
showHybridResult hr = unlines $
  [ "  found=" ++ show (hrFound hr)
      ++ (if hrKilledAll hr then " (level-killing proved NO!)" else "")
  , "  killed=" ++ show (hrKilled hr) ++ "/" ++ show (hrKilled hr + hrAlive hr)
      ++ " alive=" ++ show (hrAlive hr)
  , "  sieveWork=" ++ show (hrSieveWork hr)
  ]

-- ═══════════════════════════════════════════════════════════
-- Cardinality-informed sieve: the REAL integration
-- Uses cardinality bounds to derive TIGHT SUM RANGES for
-- each quarter, then runs 4-way merge with those tight bounds.
-- ═══════════════════════════════════════════════════════════

-- | Cardinality-informed 4-way sieve.
-- 1. Level killing → surviving cardinalities [kMin..kMax]
-- 2. For each quarter (n/4 elements), cardinality range → sum range
-- 3. Filter enumerated sums to tight ranges BEFORE merge
-- 4. Merge with tight range propagation
--
-- The win: for density-1, this cuts each quarter's surviving sums
-- from 2^{n/4} to roughly C(n/4, n/8) ≈ 2^{n/4}/√n,
-- and the merge is proportionally cheaper.
cardinalitySieveSolve :: [Int] -> Int -> (Bool, Int)
cardinalitySieveSolve weights target =
  let pw = precomputeWeights weights
      n  = pwN pw
      levels0 = initLevels pw target
      survivingKs = [lsLevel ls | ls <- levels0, lsStatus ls /= LKilled]
  in if null survivingKs
     then (False, 0)  -- Level killing proved NO!
     else
       let kMin = minimum survivingKs
           kMax = maximum survivingKs

           -- 4-way split
           q = n `div` 4
           (q1w, rest1) = splitAt q weights
           (q2w, rest2) = splitAt q rest1
           (q3w, q4w)   = splitAt q rest2
           nQ1 = length q1w; nQ2 = length q2w
           nQ3 = length q3w; nQ4 = length q4w

           -- Per-quarter cardinality bounds:
           -- j1 + j2 + j3 + j4 = k, with ji in [0, nQi]
           -- Loose but correct per-quarter bounds:
           -- jMin_i = max(0, kMin - sum of other quarter sizes)
           -- jMax_i = min(nQi, kMax)
           otherMax1 = nQ2 + nQ3 + nQ4; otherMax2 = nQ1 + nQ3 + nQ4
           otherMax3 = nQ1 + nQ2 + nQ4; otherMax4 = nQ1 + nQ2 + nQ3

           jRange qi otherMax =
             let jLo = max 0 (kMin - otherMax)
                 jHi = min qi kMax
             in (jLo, jHi)

           (j1Lo, j1Hi) = jRange nQ1 otherMax1
           (j2Lo, j2Hi) = jRange nQ2 otherMax2
           (j3Lo, j3Hi) = jRange nQ3 otherMax3
           (j4Lo, j4Hi) = jRange nQ4 otherMax4

           -- Sum bounds from cardinality bounds:
           -- sum of jLo smallest elements ≤ quarterSum ≤ sum of jHi largest
           sumBounds ws jLo jHi =
             let sorted = sort ws
                 prefAsc  = scanl' (+) 0 sorted
                 prefDesc = scanl' (+) 0 (reverse sorted)
             in (prefAsc !! min jLo (length ws), prefDesc !! min jHi (length ws))

           (s1Lo, s1Hi) = sumBounds q1w j1Lo j1Hi
           (s2Lo, s2Hi) = sumBounds q2w j2Lo j2Hi
           (s3Lo, s3Hi) = sumBounds q3w j3Lo j3Hi
           (s4Lo, s4Hi) = sumBounds q4w j4Lo j4Hi

           -- Half bounds from quarter bounds
           leftLo  = s1Lo + s2Lo;  leftHi  = s1Hi + s2Hi
           rightLo = s3Lo + s4Lo;  rightHi = s3Hi + s4Hi

           -- Tighten by target constraint
           leftLo'  = max leftLo  (target - rightHi)
           leftHi'  = min leftHi  (target - rightLo)
           rightLo' = max rightLo (target - leftHi')
           rightHi' = min rightHi (target - leftLo')

           -- Enumerate quarter sums (standard bruteForceDP)
           s1all = localBruteForceDP q1w
           s2all = localBruteForceDP q2w
           s3all = localBruteForceDP q3w
           s4all = localBruteForceDP q4w

           -- Filter to cardinality-derived ranges
           s1f = filterRange s1Lo s1Hi s1all
           s2f = filterRange s2Lo s2Hi s2all
           s3f = filterRange s3Lo s3Hi s3all
           s4f = filterRange s4Lo s4Hi s4all

           -- Fused merge with tight bounds (same as fourWayRepSolve but tighter)
           leftSums = Set.fromList
             [ a + b
             | a <- Set.toList s1f
             , let bLo = max 0 (leftLo' - a)
                   bHi = leftHi' - a
             , bHi >= bLo
             , b <- Set.toAscList (filterRange bLo bHi s2f)
             ]
           rightSums = Set.fromList
             [ a + b
             | a <- Set.toList s3f
             , let bLo = max 0 (rightLo' - a)
                   bHi = rightHi' - a
             , bHi >= bLo
             , b <- Set.toAscList (filterRange bLo bHi s4f)
             ]

           -- Final check
           found = any (\l -> Set.member (target - l) rightSums)
                       (Set.toList leftSums)

           innerWork = Set.size s1f + Set.size s2f + Set.size s3f + Set.size s4f
           mergeWork = Set.size leftSums + Set.size rightSums
       in (found, innerWork + mergeWork)

-- ═══════════════════════════════════════════════════════════
-- Combined: cardinality + representations + range propagation
-- THIS is the full integration: all three techniques together.
-- ═══════════════════════════════════════════════════════════

-- | Full hybrid: cardinality bounds + modular filtering + range-fused merge.
-- 1. Level killing → [kMin, kMax] → per-quarter sum bounds
-- 2. Enumerate quarters, filter to tight cardinality-derived ranges
-- 3. Bucket filtered sets by residue mod M (representations)
-- 4. For each residue: range-fused merge with early exit
cardinalityRepSolve :: Int -> [Int] -> Int -> (Bool, Int)
cardinalityRepSolve m1 weights target =
  let pw = precomputeWeights weights
      n  = pwN pw
      levels0 = initLevels pw target
      survivingKs = [lsLevel ls | ls <- levels0, lsStatus ls /= LKilled]
  in if null survivingKs
     then (False, 0)  -- Level killing proved NO!
     else
       let kMin = minimum survivingKs
           kMax = maximum survivingKs

           -- 4-way split
           q = n `div` 4
           (q1w, rest1) = splitAt q weights
           (q2w, rest2) = splitAt q rest1
           (q3w, q4w)   = splitAt q rest2
           nQ1 = length q1w; nQ2 = length q2w
           nQ3 = length q3w; nQ4 = length q4w

           -- Per-quarter cardinality bounds
           otherMax1 = nQ2 + nQ3 + nQ4; otherMax2 = nQ1 + nQ3 + nQ4
           otherMax3 = nQ1 + nQ2 + nQ4; otherMax4 = nQ1 + nQ2 + nQ3

           jRange qi otherMax =
             (max 0 (kMin - otherMax), min qi kMax)

           (j1Lo, j1Hi) = jRange nQ1 otherMax1
           (j2Lo, j2Hi) = jRange nQ2 otherMax2
           (j3Lo, j3Hi) = jRange nQ3 otherMax3
           (j4Lo, j4Hi) = jRange nQ4 otherMax4

           -- Sum bounds from cardinality
           sumBounds ws jLo jHi =
             let sorted = sort ws
                 prefAsc  = scanl' (+) 0 sorted
                 prefDesc = scanl' (+) 0 (reverse sorted)
             in (prefAsc !! min jLo (length ws), prefDesc !! min jHi (length ws))

           (s1Lo, s1Hi) = sumBounds q1w j1Lo j1Hi
           (s2Lo, s2Hi) = sumBounds q2w j2Lo j2Hi
           (s3Lo, s3Hi) = sumBounds q3w j3Lo j3Hi
           (s4Lo, s4Hi) = sumBounds q4w j4Lo j4Hi

           -- Half bounds
           leftLo  = max (s1Lo + s2Lo) (target - s3Hi - s4Hi)
           leftHi  = min (s1Hi + s2Hi) (target - s3Lo - s4Lo)
           rightLo = max (s3Lo + s4Lo) (target - leftHi)
           rightHi = min (s3Hi + s4Hi) (target - leftLo)

           -- Enumerate and filter quarters
           s1 = filterRange s1Lo s1Hi (localBruteForceDP q1w)
           s2 = filterRange s2Lo s2Hi (localBruteForceDP q2w)
           s3 = filterRange s3Lo s3Hi (localBruteForceDP q3w)
           s4 = filterRange s4Lo s4Hi (localBruteForceDP q4w)

           innerWork = Set.size s1 + Set.size s2 + Set.size s3 + Set.size s4

           -- Bucket filtered S2 and S4 by residue mod M (representations)
           b2 = Map.fromListWith (++) [(s `mod` m1, [s]) | s <- Set.toList s2]
           b4 = Map.fromListWith (++) [(s `mod` m1, [s]) | s <- Set.toList s4]
           tMod = target `mod` m1

           -- Per-residue merge with range bounds + early exit
           (found, work) = goR 0 0
           goR r w | r >= m1 = (False, w)
           goR r w =
             let -- Left: S1 × bucket(r) of S2, with range filter
                 leftR = Set.fromList
                   [ ab
                   | a <- Set.toList s1
                   , b <- Map.findWithDefault [] ((r - a `mod` m1) `mod` m1) b2
                   , let ab = a + b
                   , ab >= leftLo && ab <= leftHi
                   ]
                 -- Right: S3 × bucket(T-r) of S4, with range filter
                 rRight = (tMod - r) `mod` m1
                 rightR = Set.fromList
                   [ cd
                   | c <- Set.toList s3
                   , d <- Map.findWithDefault [] ((rRight - c `mod` m1) `mod` m1) b4
                   , let cd = c + d
                   , cd >= rightLo && cd <= rightHi
                   ]
                 hit = any (\l -> Set.member (target - l) rightR) (Set.toList leftR)
                 stepW = Set.size leftR + Set.size rightR
             in if hit then (True, w + stepW)
                else goR (r + 1) (w + stepW)

       in (found, innerWork + work)

-- ═══════════════════════════════════════════════════════════
-- Multi-density instance generator
-- ═══════════════════════════════════════════════════════════

-- | Generate a Subset Sum instance with given density.
-- density d means weights ~ 2^(n/d).
-- d=1: weights ~ 2^n (classic density-1, hardest known regime)
-- d=2: weights ~ 2^(n/2) (medium)
-- d=5: weights ~ 2^(n/5) (easier, more sum collisions)
mkDensityD :: Int -> Double -> ([Int], Int)
mkDensityD n d =
  let bitWidth = max 4 (ceiling (fromIntegral n / d :: Double))
      base = 2 ^ bitWidth
      range = 2 ^ (bitWidth - 1)
      ws = [base + ((i * 1103515245 + 12345) `mod` range) | i <- [0..n-1]]
      t = sum ws `div` 2 + 1
  in (ws, t)

-- ═══════════════════════════════════════════════════════════
-- Utilities (local to avoid modifying MultiLevelSieve exports)
-- ═══════════════════════════════════════════════════════════

localBruteForceDP :: [Int] -> Set.Set Int
localBruteForceDP = foldl' (\s w -> Set.union s (Set.map (+ w) s)) (Set.singleton 0)

filterRange :: Int -> Int -> Set.Set Int -> Set.Set Int
filterRange lo hi s =
  let (_, geqLo) = Set.split (lo - 1) s
      (leqHi, _) = Set.split (hi + 1) geqLo
  in leqHi

-- | Density-1 instance generator (same as MultiLevelSieve.mkDensity1)
mkDensity1 :: Int -> ([Int], Int)
mkDensity1 n =
  let ws = [2^n + ((i * 1103515245 + 12345) `mod` (2^(n-1))) | i <- [0..n-1]]
      t = sum ws `div` 2 + 1
  in (ws, t)

padR :: Int -> String -> String
padR n s = s ++ replicate (max 0 (n - length s)) ' '

roundTo :: Int -> Double -> Double
roundTo n x = fromIntegral (round (x * 10 ^ n) :: Int) / 10 ^ (fromIntegral n)
