module PeqNP.Diagonal
  ( Strategy(..)
  , runStrategy
  , DiagonalResult(..)
  , defeat
  , diagonalExperiment
  , showDiagonalResults
  -- * Built-in strategies
  , greedyLargest
  , greedySmallest
  , alwaysInclude
  , alwaysSkip
  , thresholdHalf
  , alternating
  ) where

import qualified Data.Set as Set

import PeqNP.DPSolver (dpReachable)

-- | A deterministic strategy for Subset Sum.
-- Given partial sum and next element, decides: include or skip?
data Strategy = Strategy
  { stratName   :: String
  , stratDecide :: Int -> Int -> Int -> Bool
    -- ^ partialSum -> element -> target -> include?
  }

-- | Run a strategy on an instance: apply decisions left to right
runStrategy :: Strategy -> [Int] -> Int -> (Bool, [Int])
runStrategy strat elems target = go 0 [] elems
  where
    go partialSum included [] =
      (partialSum == target, reverse included)
    go partialSum included (x:xs) =
      if stratDecide strat partialSum x target
        then go (partialSum + x) (x : included) xs
        else go partialSum included xs

-- | Result of the diagonal argument for one strategy
data DiagonalResult = DR
  { drStrategy      :: String
  , drDefeatedAtN   :: Maybe Int         -- min n where strategy fails
  , drCounterexample :: Maybe ([Int], Int, Bool)  -- (elements, target, correct answer)
  } deriving (Show)

-- | THE DIAGONAL ARGUMENT: find an instance where the strategy gives wrong answer.
--
-- For each n = 2, 3, ..., maxN:
--   generate candidate instances and test if strategy gets it wrong.
--   An instance "defeats" the strategy if:
--     runStrategy gives YES but correct answer is NO, or vice versa.
defeat :: Strategy -> Int -> Maybe ([Int], Int, Bool)
defeat strat maxN = go 2
  where
    go n | n > maxN = Nothing
    go n =
      case findCounterexample strat n of
        Just result -> Just result
        Nothing     -> go (n + 1)

    findCounterexample :: Strategy -> Int -> Maybe ([Int], Int, Bool)
    findCounterexample s n =
      let -- Generate challenging instances of size n
          instances = challengingInstances n
      in firstJust (testInstance s) instances

    testInstance :: Strategy -> ([Int], Int) -> Maybe ([Int], Int, Bool)
    testInstance s (es, t) =
      let (stratAnswer, _) = runStrategy s es t
          realAnswer = Set.member t (dpReachable es)
      in if stratAnswer /= realAnswer
         then Just (es, t, realAnswer)
         else Nothing

    firstJust :: (a -> Maybe b) -> [a] -> Maybe b
    firstJust _ [] = Nothing
    firstJust f (x:xs) = case f x of
      Just r  -> Just r
      Nothing -> firstJust f xs

-- | Generate challenging instances of size n for testing strategies
challengingInstances :: Int -> [([Int], Int)]
challengingInstances n =
  let -- Fibonacci-like weights (hard for greedy)
      fibs = take n $ drop 2 $ map fst $ iterate (\(a,b) -> (b, a+b)) (0,1)
      fibSum = sum fibs
      -- Various targets: reachable and unreachable
      reachable = Set.toList $ dpReachable fibs
      unreachable = [t | t <- [1..fibSum+1], not (Set.member t (dpReachable fibs))]
      -- Powers of 2 (hard for modular strategies)
      pows = take n [2^i | i <- [(0 :: Int)..]]
      powReachable = Set.toList $ dpReachable pows
      powUnreachable = [t | t <- [1..sum pows + 1], not (Set.member t (dpReachable pows))]
      -- Sequential (dense sums)
      seqs = [1..n]
      seqReachable = Set.toList $ dpReachable seqs
      seqUnreachable = [t | t <- [1..sum seqs + 1], not (Set.member t (dpReachable seqs))]
  in    [(fibs, t) | t <- take 5 reachable ++ take 5 unreachable]
     ++ [(pows, t) | t <- take 5 powReachable ++ take 5 powUnreachable]
     ++ [(seqs, t) | t <- take 5 seqReachable ++ take 5 seqUnreachable]

-- | Run diagonal argument against multiple strategies
diagonalExperiment :: [Strategy] -> [DiagonalResult]
diagonalExperiment strategies =
  [ DR (stratName s) (fmap (\(es,_,_) -> length es) result) result
  | s <- strategies
  , let result = defeat s 12
  ]

-- ═══════════════════════════════════════════════════════════
-- Built-in strategies
-- ═══════════════════════════════════════════════════════════

-- | Always include if it doesn't exceed target
greedyLargest :: Strategy
greedyLargest = Strategy "greedy-largest" $ \ps x t -> ps + x <= t

-- | Include smallest elements first (sort-dependent, but test on original order)
greedySmallest :: Strategy
greedySmallest = Strategy "greedy-smallest" $ \ps x t -> ps + x <= t && x <= t `div` 2

-- | Always include everything
alwaysInclude :: Strategy
alwaysInclude = Strategy "always-include" $ \_ _ _ -> True

-- | Always skip everything
alwaysSkip :: Strategy
alwaysSkip = Strategy "always-skip" $ \_ _ _ -> False

-- | Include if element ≤ target/2
thresholdHalf :: Strategy
thresholdHalf = Strategy "threshold-half" $ \_ x t -> x <= t `div` 2

-- | Alternate include/skip
alternating :: Strategy
alternating = Strategy "alternating" $ \ps _ _ -> even ps

showDiagonalResults :: [DiagonalResult] -> String
showDiagonalResults results = unlines $
  [ "  " ++ padR 20 "Strategy" ++ padR 12 "Defeated at" ++ "Counterexample"
  , "  " ++ replicate 60 '-'
  ] ++
  [ "  " ++ padR 20 (drStrategy r)
    ++ padR 12 (maybe "survived" (\n -> "n=" ++ show n) (drDefeatedAtN r))
    ++ case drCounterexample r of
         Nothing -> "none found"
         Just (es, t, ans) -> show es ++ " t=" ++ show t ++ " ans=" ++ show ans
  | r <- results
  ]

padR :: Int -> String -> String
padR n s = s ++ replicate (max 0 (n - length s)) ' '
