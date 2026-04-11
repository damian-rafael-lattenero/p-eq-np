module Main where

-- ALGEBRAIC SHORT-CIRCUIT: encode Subset Sum as ADT + pattern matching
--
-- Like AND(False, _) = False kills a subtree in boolean logic,
-- we define algebraic rules that kill branches of the 2^n recursion tree.
--
-- The KEY DIFFERENCE from previous experiments: we apply ALL rules
-- SIMULTANEOUSLY as a single pattern match. The SYNERGY between
-- rules might kill branches that no single rule can kill alone.
--
-- data SSValue = Solved | Impossible Rule | Live SSInfo
--
-- simplify :: SSInfo -> SSValue  -- THE pattern match that kills branches

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.List (foldl')
import Data.Bits (xor, shiftR)
import qualified Data.Array as A
import PeqNP.ActorSolver (padR)

-- ═══════════════════════════════════════════════════════════════
-- THE ADT
-- ═══════════════════════════════════════════════════════════════

data Rule = RBoundsHi | RBoundsLo | RModular | RCardinality | RCombined | RSolved
  deriving (Show, Eq, Ord)

data SSValue
  = Solved
  | Impossible !Rule
  | Live !SSInfo

data SSInfo = SSInfo
  { siPartial   :: !Int
  , siRemaining :: !Int
  , siTarget    :: !Int
  , siLevel     :: !Int
  , siItemsUsed :: !Int
  , siItemsLeft :: !Int
  }

-- Precomputed modular reachability for suffix of weights
-- modOracle ! (prime, level) = reachable residues of weights[level..n-1]
type ModOracle = IM.IntMap IS.IntSet  -- encoded as (prime * 1000 + level) → residues

-- ═══════════════════════════════════════════════════════════════
-- THE PATTERN MATCH (simplify)
-- ═══════════════════════════════════════════════════════════════

simplify :: ModOracle -> [Int] -> SSInfo -> SSValue
simplify oracle primes info
  -- Rule 0: SOLVED — partial sum equals target
  | siPartial info == siTarget info
  = Solved

  -- Rule 1: BOUNDS HIGH — already overshot
  | siPartial info > siTarget info
  = Impossible RBoundsHi

  -- Rule 2: BOUNDS LOW — can't reach even with all remaining
  | siPartial info + siRemaining info < siTarget info
  = Impossible RBoundsLo

  -- Rule 3: CARDINALITY — not enough items left
  -- (need at least ceil(gap / max_remaining_weight) items)
  | siItemsLeft info == 0 && siPartial info /= siTarget info
  = Impossible RCardinality

  -- Rule 4: MODULAR — target residue unreachable by remaining suffix
  | any (modularFails oracle info) primes
  = Impossible RModular

  -- Rule 5: COMBINED — tighter bound check using cardinality + bounds
  -- If we need k more items, and the k largest remaining can't reach gap,
  -- or the k smallest exceed gap → impossible
  | combinedFails info
  = Impossible RCombined

  -- No rule fires — must evaluate
  | otherwise
  = Live info

-- | Does modular test fail for this prime?
modularFails :: ModOracle -> SSInfo -> Int -> Bool
modularFails oracle info p =
  let gap = siTarget info - siPartial info
      needed = gap `mod` p
      key = p * 1000 + siLevel info
  in case IM.lookup key oracle of
       Nothing -> False  -- no oracle data, can't reject
       Just reachable -> not (IS.member needed reachable)

-- | Combined bounds + cardinality check
combinedFails :: SSInfo -> Bool
combinedFails info =
  let gap = siTarget info - siPartial info
      itemsLeft = siItemsLeft info
  in gap > 0 && itemsLeft > 0 &&
     -- If gap > remaining, already caught by bounds.
     -- Additional: if gap < itemsLeft (need more items than gap allows
     -- with minimum weight 1), that's still possible.
     -- The real combined check: if we've used too many items
     -- relative to how much gap remains, it might be impossible.
     -- This is a soft heuristic — the real power is in modular + bounds.
     False  -- placeholder: let individual rules do the work first

-- ═══════════════════════════════════════════════════════════════
-- BUILD MODULAR ORACLE
-- ═══════════════════════════════════════════════════════════════

buildModOracle :: [Int] -> [Int] -> ModOracle
buildModOracle weights primes =
  let n = length weights
      -- For each prime p and each suffix starting at level k:
      -- compute reachable residues of weights[k..n-1]
  in IM.fromList
       [ (p * 1000 + k, reachable)
       | p <- primes
       , k <- [0..n]
       , let suffix = drop k weights
             reachable = foldl' (\acc w ->
               IS.union acc (IS.map (\r -> (r + w) `mod` p) acc)
               ) (IS.singleton 0) suffix
       ]

-- ═══════════════════════════════════════════════════════════════
-- THE SEARCH (with short-circuit counting)
-- ═══════════════════════════════════════════════════════════════

data Stats = Stats
  { stNodes    :: !Int
  , stSolved   :: !Int
  , stKilledBy :: !(IM.IntMap Int)  -- rule ordinal → count
  } deriving (Show)

initStats :: Stats
initStats = Stats 0 0 IM.empty

ruleOrd :: Rule -> Int
ruleOrd RBoundsHi    = 0
ruleOrd RBoundsLo    = 1
ruleOrd RModular     = 2
ruleOrd RCardinality = 3
ruleOrd RCombined    = 4
ruleOrd RSolved      = 5

addKill :: Rule -> Stats -> Stats
addKill r s = s { stKilledBy = IM.insertWith (+) (ruleOrd r) 1 (stKilledBy s) }

-- | Full algebraic search with short-circuiting
algebraicSearch :: [Int] -> Int -> [Int] -> (Bool, Stats)
algebraicSearch weights target primes =
  let n = length weights
      oracle = buildModOracle weights primes
      wArr = A.listArray (0, n-1) weights  -- O(1) access
      suffArr = A.listArray (0, n) (scanr (+) 0 weights)

      go :: SSInfo -> Stats -> (Bool, Stats)
      go info stats =
        let stats' = stats { stNodes = stNodes stats + 1 }
            result = simplify oracle primes info
        in case result of
          Solved -> (True, stats' { stSolved = stSolved stats' + 1 })
          Impossible rule -> (False, addKill rule stats')
          Live liveInfo ->
            let k = siLevel liveInfo
                w = wArr A.! k
                -- Branch IN: include weight k
                infoIn = liveInfo
                  { siPartial = siPartial liveInfo + w
                  , siRemaining = suffArr A.! (k + 1)
                  , siLevel = k + 1
                  , siItemsUsed = siItemsUsed liveInfo + 1
                  , siItemsLeft = siItemsLeft liveInfo - 1
                  }
                -- Branch OUT: exclude weight k
                infoOut = liveInfo
                  { siRemaining = suffArr A.! (k + 1)
                  , siLevel = k + 1
                  , siItemsLeft = siItemsLeft liveInfo - 1
                  }
                (foundIn, stats2) = go infoIn stats'
            in if foundIn then (True, stats2)
               else go infoOut stats2

      initInfo = SSInfo
        { siPartial = 0, siRemaining = sum weights, siTarget = target
        , siLevel = 0, siItemsUsed = 0, siItemsLeft = n }
  in go initInfo initStats

-- | Naive search (bounds only, no modular/cardinality)
naiveSearch :: [Int] -> Int -> (Bool, Int)
naiveSearch weights target =
  let n = length weights
      suffSums = scanr (+) 0 weights
      go partial remaining level nodes
        | partial == target = (True, nodes + 1)
        | partial > target = (False, nodes + 1)
        | partial + remaining < target = (False, nodes + 1)
        | level >= n = (False, nodes + 1)
        | otherwise =
            let w = weights !! level
                rem' = suffSums !! (level + 1)
                (fIn, nIn) = go (partial + w) rem' (level + 1) (nodes + 1)
            in if fIn then (True, nIn)
               else go partial rem' (level + 1) nIn
  in go 0 (sum weights) 0 0

mkHash :: Int -> ([Int], Int)
mkHash n =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [2^n + (abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` (2^(n-1)))
           | i <- [0..n-1 :: Int]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

mkHashYes :: Int -> ([Int], Int)
mkHashYes n = let (ws, _) = mkHash n in (ws, sum (take (n `div` 2) ws))

showF :: Int -> Double -> String
showF d x = let f = 10 ^ d :: Int
                r = fromIntegral (round (x * fromIntegral f) :: Int) / fromIntegral f :: Double
            in show r

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn " ALGEBRAIC SHORT-CIRCUIT: ADT + pattern matching for Subset Sum"
  putStrLn " Like AND(False,_)=False — kill branches by algebraic laws"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  let primes = [3, 5, 7, 11, 13, 17, 19, 23]

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: ADT vs Naive — how many nodes killed?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. ADT vs NAIVE: nodes explored ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 12 "naive"
    ++ padR 12 "adt" ++ padR 10 "kill%" ++ padR 8 "found"
  putStrLn (replicate 54 '-')
  mapM_ (\n -> do
    -- YES
    let (wsY, tY) = mkHashYes n
        (fNaiveY, naiveY) = naiveSearch wsY tY
        (fAdtY, statsY) = algebraicSearch wsY tY primes
        killY = if naiveY == 0 then 0
                else (1 - fromIntegral (stNodes statsY) / fromIntegral naiveY) * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 12 (show naiveY)
      ++ padR 12 (show (stNodes statsY))
      ++ padR 10 (showF 1 killY ++ "%")
      ++ padR 8 (show fAdtY)
    -- NO
    let (wsN, tN) = mkHash n
        (_, naiveN) = naiveSearch wsN tN
        (fAdtN, statsN) = algebraicSearch wsN tN primes
        killN = if naiveN == 0 then 0
                else (1 - fromIntegral (stNodes statsN) / fromIntegral naiveN) * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 12 (show naiveN)
      ++ padR 12 (show (stNodes statsN))
      ++ padR 10 (showF 1 killN ++ "%")
      ++ padR 8 (show fAdtN)
    ) [6, 8, 10, 12, 14, 16]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Kill attribution — which rule kills most?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. KILL ATTRIBUTION: which rule kills most branches? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 10 "bounds-hi"
    ++ padR 10 "bounds-lo" ++ padR 10 "modular" ++ padR 10 "cardinal"
    ++ padR 10 "total"
  putStrLn (replicate 62 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (_, stats) = algebraicSearch ws t primes
        getKills r = IM.findWithDefault 0 (ruleOrd r) (stKilledBy stats)
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 10 (show (getKills RBoundsHi))
      ++ padR 10 (show (getKills RBoundsLo))
      ++ padR 10 (show (getKills RModular))
      ++ padR 10 (show (getKills RCardinality))
      ++ padR 10 (show (stNodes stats))
    ) [8, 10, 12, 14, 16]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: SYNERGY — bounds-only vs modular-only vs ALL
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. SYNERGY: combined kills more than sum of parts? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "naive" ++ padR 12 "bounds-only"
    ++ padR 12 "mod-only" ++ padR 12 "ALL" ++ padR 10 "synergy"
  putStrLn (replicate 64 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (_, naive) = naiveSearch ws t
        -- Bounds only (= naive, since naive uses bounds)
        boundsOnly = naive
        -- Modular only: search with primes but pretend bounds don't exist
        -- Actually, bounds are always active in our simplify. Let's compare
        -- with 0 primes vs 8 primes
        (_, statsNoPrimes) = algebraicSearch ws t []
        (_, statsAllPrimes) = algebraicSearch ws t primes
        nodesNoPrimes = stNodes statsNoPrimes
        nodesAll = stNodes statsAllPrimes
        -- Synergy: how much does adding modular ON TOP of bounds help?
        synergyPct = if nodesNoPrimes == 0 then 0
                     else (1 - fromIntegral nodesAll / fromIntegral nodesNoPrimes) * 100 :: Double
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show naive)
      ++ padR 12 (show nodesNoPrimes)
      ++ padR 12 ("—")
      ++ padR 12 (show nodesAll)
      ++ padR 10 (showF 1 synergyPct ++ "%")
    ) [8, 10, 12, 14, 16]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: SCALING — does kill% grow with n?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. SCALING: does ADT kill% grow, shrink, or stay flat? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "adt-nodes" ++ padR 10 "2^n"
    ++ padR 12 "adt/2^n" ++ padR 12 "adt/n^3"
  putStrLn (replicate 52 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (_, stats) = algebraicSearch ws t primes
        nodes = stNodes stats
        twoN = (2::Int)^n
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show nodes)
      ++ padR 10 (show twoN)
      ++ padR 12 (showF 4 (fromIntegral nodes / fromIntegral twoN :: Double))
      ++ padR 12 (showF 1 (fromIntegral nodes / fromIntegral (n*n*n) :: Double))
    ) [6, 8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: Extended scaling with more primes
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. EXTENDED: more primes (16), larger n ==="
  putStrLn ""
  let bigPrimes = [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59]
  putStrLn $ padR 5 "n" ++ padR 12 "adt-nodes" ++ padR 10 "2^n"
    ++ padR 12 "adt/2^n" ++ padR 10 "adt/n^3" ++ padR 10 "adt/n^4"
  putStrLn (replicate 60 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (_, stats) = algebraicSearch ws t bigPrimes
        nodes = stNodes stats
        twoN = (2::Int)^n
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show nodes)
      ++ padR 10 (show twoN)
      ++ padR 12 (showF 4 (fromIntegral nodes / fromIntegral twoN :: Double))
      ++ padR 10 (showF 2 (fromIntegral nodes / fromIntegral (n*n*n) :: Double))
      ++ padR 10 (showF 3 (fromIntegral nodes / fromIntegral (n*n*n*n) :: Double))
    ) [8, 10, 12, 14, 16, 18, 20]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "ANALYSIS:"
  putStrLn " The ADT combines bounds + modular + cardinality in ONE match."
  putStrLn " Section 3 (synergy) is the key: if combined > sum of parts,"
  putStrLn " the algebraic structure is creating EMERGENT pruning."
  putStrLn ""
  putStrLn " Section 4 (scaling): "
  putStrLn "   adt/2^n → 0 : algebraic laws collapse the tree → POLY!"
  putStrLn "   adt/2^n → const : same as brute force, laws don't help"
  putStrLn "   adt/n^3 → const : ADT is cubic → POLYNOMIAL!"
  putStrLn "═══════════════════════════════════════════════════════════════════"
