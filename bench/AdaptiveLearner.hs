module Main where

{-
  ADAPTIVE LEARNER: Ask the wall questions, learn from answers

  Like a SAT solver's CDCL: when a partial assignment contradicts,
  learn WHY (extract a "no-good" set of choices) and never repeat
  that pattern again. Each learned fact eliminates a FAMILY of paths.

  Also: precompute small-subset "rainbow tables" — hash partial sums
  to know instantly if a residual is achievable by a small group.

  Three comparison points:
    1. NAIVE: backtracking + bounds only
    2. RAINBOW: + precomputed partial-sum lookups for small groups
    3. CDCL: + conflict-driven clause learning

  KEY QUESTION: do learned clauses accumulate fast enough to collapse 2^n?
-}

import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as Set
import Data.List (foldl', minimumBy)
import Data.Ord (comparing)
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

-- ═══════════════════════════════════════════════════════════════
-- SECTION A: NAIVE BACKTRACKING (bounds only)
-- ═══════════════════════════════════════════════════════════════

naiveSearch :: [Int] -> Int -> (Bool, Int)  -- (found, nodes_explored)
naiveSearch weights target =
  let n = length weights
      -- Precompute suffix sums for bound checking
      suffSums = listArray n weights
      go rem idx nodes
        | rem == 0  = (True, nodes + 1)
        | rem < 0   = (False, nodes + 1)
        | idx >= n  = (False, nodes + 1)
        | rem > suffSums IM.! idx = (False, nodes + 1)  -- can't reach even with all remaining
        | otherwise =
            let w = weights !! idx
                -- Try IN
                (fIn, nIn) = go (rem - w) (idx + 1) (nodes + 1)
            in if fIn then (True, nIn)
               else go rem (idx + 1) nIn  -- Try OUT
  in go target 0 0
  where
    -- suffix sum from index i: sum of weights[i..n-1]
    listArray n ws =
      let suf = scanr (+) 0 ws
      in IM.fromList (zip [0..n] suf)

-- ═══════════════════════════════════════════════════════════════
-- SECTION B: RAINBOW TABLE — precompute group achievability
-- ═══════════════════════════════════════════════════════════════

-- | Split weights into groups of size g. For each group, precompute
-- ALL achievable sums (2^g per group). During search, when residual
-- matches a group's precomputed sum, shortcut to YES.
type Rainbow = IM.IntMap IS.IntSet  -- group_id → set of achievable sums

buildRainbow :: [Int] -> Int -> Rainbow
buildRainbow weights groupSize =
  let groups = chunk groupSize weights
      groupSums = map allSubsetSums groups
  in IM.fromList (zip [0..] groupSums)

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk n xs = let (a, b) = splitAt n xs in a : chunk n b

allSubsetSums :: [Int] -> IS.IntSet
allSubsetSums [] = IS.singleton 0
allSubsetSums (w:ws) = let rest = allSubsetSums ws
                       in IS.union rest (IS.map (+w) rest)

-- Search with rainbow table assist
rainbowSearch :: [Int] -> Int -> Int -> (Bool, Int, Int)
-- Returns: (found, nodes, rainbow_hits)
rainbowSearch weights target groupSize =
  let n = length weights
      rainbow = buildRainbow weights groupSize
      nGroups = IM.size rainbow
      suffSums = IM.fromList (zip [0..n] (scanr (+) 0 weights))

      -- At each depth, check if remaining target is achievable by
      -- any single remaining group (cheap lookup)
      checkRainbow rem idx =
        let groupIdx = idx `div` groupSize
        in any (\gi ->
          let sums = rainbow IM.! gi
          in IS.member rem sums
          ) [groupIdx .. nGroups - 1]

      go rem idx nodes hits
        | rem == 0  = (True, nodes + 1, hits)
        | rem < 0   = (False, nodes + 1, hits)
        | idx >= n  = (False, nodes + 1, hits)
        | rem > suffSums IM.! idx = (False, nodes + 1, hits)
        -- Rainbow shortcut: if remaining matches exactly one group's sum
        | idx `mod` groupSize == 0 && idx + groupSize <= n =
            let gi = idx `div` groupSize
                sums = rainbow IM.! gi
            in if IS.member rem sums
               then (True, nodes + 1, hits + 1)  -- found via rainbow!
               else let w = weights !! idx
                        (fIn, nIn, hIn) = go (rem - w) (idx + 1) (nodes + 1) hits
                    in if fIn then (True, nIn, hIn)
                       else go rem (idx + 1) nIn hIn
        | otherwise =
            let w = weights !! idx
                (fIn, nIn, hIn) = go (rem - w) (idx + 1) (nodes + 1) hits
            in if fIn then (True, nIn, hIn)
               else go rem (idx + 1) nIn hIn
  in go target 0 0 0

-- ═══════════════════════════════════════════════════════════════
-- SECTION C: CDCL — learn from conflicts
-- ═══════════════════════════════════════════════════════════════

-- A clause: "these indices being ALL IN leads to failure"
-- If current in-set is superset of clause → prune
type Clause = IS.IntSet

data CDCLState = CS
  { csNodes   :: !Int
  , csClauses :: ![Clause]
  , csLearned :: !Int
  , csPruned  :: !Int
  }

initCS :: CDCLState
initCS = CS 0 [] 0 0

-- | Check if current in-set triggers any learned clause
blocked :: [Clause] -> IS.IntSet -> Bool
blocked clauses inSet = any (`IS.isSubsetOf` inSet) clauses

-- | CDCL search
cdclSearch :: [Int] -> Int -> (Bool, CDCLState)
cdclSearch weights target =
  let n = length weights
      suffSums = IM.fromList (zip [0..n] (scanr (+) 0 weights))

      go :: IS.IntSet -> Int -> Int -> CDCLState -> (Bool, CDCLState, Maybe Clause)
      -- Returns: (found, state, maybe_learned_clause)
      go inSet rem idx cs
        | rem == 0  = (True, cs { csNodes = csNodes cs + 1 }, Nothing)
        | rem < 0   =
            -- Conflict! Learn: this in-set is bad
            let clause = inSet
                cs' = cs { csNodes = csNodes cs + 1
                         , csLearned = csLearned cs + 1
                         , csClauses = clause : csClauses cs }
            in (False, cs', Just clause)
        | idx >= n  =
            let clause = inSet
                cs' = cs { csNodes = csNodes cs + 1
                         , csLearned = csLearned cs + 1
                         , csClauses = clause : csClauses cs }
            in (False, cs', Just clause)
        | rem > suffSums IM.! idx =
            let clause = inSet
                cs' = cs { csNodes = csNodes cs + 1
                         , csLearned = csLearned cs + 1
                         , csClauses = clause : csClauses cs }
            in (False, cs', Just clause)
        | blocked (csClauses cs) inSet =
            -- Pruned by learned clause!
            (False, cs { csNodes = csNodes cs + 1, csPruned = csPruned cs + 1 }, Nothing)
        | otherwise =
            let cs1 = cs { csNodes = csNodes cs + 1 }
                w = weights !! idx
                -- Try IN
                inSet' = IS.insert idx inSet
                (fIn, cs2, _) = go inSet' (rem - w) (idx + 1) cs1
            in if fIn then (True, cs2, Nothing)
               else
                -- Try OUT (clauses from IN branch carry over)
                let (fOut, cs3, cl) = go inSet rem (idx + 1) cs2
                in (fOut, cs3, cl)
  in let (found, finalCS, _) = go IS.empty target 0 initCS
     in (found, finalCS)

-- ═══════════════════════════════════════════════════════════════
-- SECTION D: COMBINED — Rainbow + CDCL
-- ═══════════════════════════════════════════════════════════════

combinedSearch :: [Int] -> Int -> Int -> (Bool, Int, Int, Int)
-- Returns: (found, nodes, rainbow_hits, clauses_learned)
combinedSearch weights target groupSize =
  let n = length weights
      rainbow = buildRainbow weights groupSize
      nGroups = IM.size rainbow
      suffSums = IM.fromList (zip [0..n] (scanr (+) 0 weights))

      go inSet rem idx cs rbHits
        | rem == 0  = (True, cs { csNodes = csNodes cs + 1 }, rbHits)
        | rem < 0   =
            let cl = inSet
                cs' = cs { csNodes = csNodes cs + 1, csLearned = csLearned cs + 1
                         , csClauses = cl : csClauses cs }
            in (False, cs', rbHits)
        | idx >= n  =
            let cs' = cs { csNodes = csNodes cs + 1 }
            in (False, cs', rbHits)
        | rem > suffSums IM.! idx =
            let cl = inSet
                cs' = cs { csNodes = csNodes cs + 1, csLearned = csLearned cs + 1
                         , csClauses = cl : csClauses cs }
            in (False, cs', rbHits)
        | blocked (csClauses cs) inSet =
            (False, cs { csNodes = csNodes cs + 1, csPruned = csPruned cs + 1 }, rbHits)
        -- Rainbow check at group boundaries
        | idx `mod` groupSize == 0 && idx + groupSize <= n =
            let gi = idx `div` groupSize
                sums = rainbow IM.! gi
            in if IS.member rem sums
               then (True, cs { csNodes = csNodes cs + 1 }, rbHits + 1)
               else
                 let w = weights !! idx
                     inSet' = IS.insert idx inSet
                     (fIn, cs2, rh2) = go inSet' (rem - w) (idx + 1)
                                          (cs { csNodes = csNodes cs + 1 }) rbHits
                 in if fIn then (True, cs2, rh2)
                    else go inSet rem (idx + 1) cs2 rh2
        | otherwise =
            let w = weights !! idx
                inSet' = IS.insert idx inSet
                (fIn, cs2, rh2) = go inSet' (rem - w) (idx + 1)
                                    (cs { csNodes = csNodes cs + 1 }) rbHits
            in if fIn then (True, cs2, rh2)
               else go inSet rem (idx + 1) cs2 rh2

      (found, finalCS, finalRB) = go IS.empty target 0 initCS 0
  in (found, csNodes finalCS, finalRB, csLearned finalCS)

-- ═══════════════════════════════════════════════════════════════

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
mkHashYes n =
  let (ws, _) = mkHash n
  in (ws, sum (take (n `div` 2) ws))

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int)
                / fromIntegral factor :: Double
  in show rounded

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn " ADAPTIVE LEARNER: ask the wall smart questions"
  putStrLn " Rainbow tables + CDCL conflict learning for Subset Sum"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Naive vs CDCL — nodes explored
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. NAIVE vs CDCL: nodes explored ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 12 "naive"
    ++ padR 12 "cdcl" ++ padR 10 "learned" ++ padR 10 "pruned"
    ++ padR 10 "save%"
  putStrLn (replicate 66 '-')
  mapM_ (\n -> do
    -- NO instance
    let (wsN, tN) = mkHash n
        (_, naiveN) = naiveSearch wsN tN
        (_, csN) = cdclSearch wsN tN
        saveN = if naiveN == 0 then 0
                else (1 - fromIntegral (csNodes csN) / fromIntegral naiveN) * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 12 (show naiveN)
      ++ padR 12 (show (csNodes csN))
      ++ padR 10 (show (csLearned csN))
      ++ padR 10 (show (csPruned csN))
      ++ padR 10 (showF 1 saveN ++ "%")
    -- YES instance
    let (wsY, tY) = mkHashYes n
        (_, naiveY) = naiveSearch wsY tY
        (_, csY) = cdclSearch wsY tY
        saveY = if naiveY == 0 then 0
                else (1 - fromIntegral (csNodes csY) / fromIntegral naiveY) * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 12 (show naiveY)
      ++ padR 12 (show (csNodes csY))
      ++ padR 10 (show (csLearned csY))
      ++ padR 10 (show (csPruned csY))
      ++ padR 10 (showF 1 saveY ++ "%")
    ) [8, 10, 12, 14, 16]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Rainbow table impact
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. RAINBOW TABLES: precomputed group sums ==="
  putStrLn "   (group_size=4: precompute 2^4=16 sums per group)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 12 "naive"
    ++ padR 12 "rainbow" ++ padR 10 "rb-hits" ++ padR 10 "save%"
  putStrLn (replicate 56 '-')
  mapM_ (\n -> do
    let gs = 4
    -- YES instance (rainbow helps most when answer exists)
    let (wsY, tY) = mkHashYes n
        (_, naiveY) = naiveSearch wsY tY
        (_, rbNodesY, rbHitsY) = rainbowSearch wsY tY gs
        saveY = if naiveY == 0 then 0
                else (1 - fromIntegral rbNodesY / fromIntegral naiveY) * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 12 (show naiveY)
      ++ padR 12 (show rbNodesY)
      ++ padR 10 (show rbHitsY)
      ++ padR 10 (showF 1 saveY ++ "%")
    -- NO instance
    let (wsN, tN) = mkHash n
        (_, naiveN) = naiveSearch wsN tN
        (_, rbNodesN, rbHitsN) = rainbowSearch wsN tN gs
        saveN = if naiveN == 0 then 0
                else (1 - fromIntegral rbNodesN / fromIntegral naiveN) * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 12 (show naiveN)
      ++ padR 12 (show rbNodesN)
      ++ padR 10 (show rbHitsN)
      ++ padR 10 (showF 1 saveN ++ "%")
    ) [8, 10, 12, 14, 16]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Combined — the full arsenal
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. FULL ARSENAL: rainbow + CDCL combined ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 12 "naive"
    ++ padR 12 "combined" ++ padR 10 "rb-hits" ++ padR 10 "learned"
    ++ padR 10 "save%"
  putStrLn (replicate 66 '-')
  mapM_ (\n -> do
    let gs = 4
    -- YES
    let (wsY, tY) = mkHashYes n
        (_, naiveY) = naiveSearch wsY tY
        (_, combNodesY, rbHY, clY) = combinedSearch wsY tY gs
        saveY = if naiveY == 0 then 0
                else (1 - fromIntegral combNodesY / fromIntegral naiveY) * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 12 (show naiveY)
      ++ padR 12 (show combNodesY)
      ++ padR 10 (show rbHY)
      ++ padR 10 (show clY)
      ++ padR 10 (showF 1 saveY ++ "%")
    -- NO
    let (wsN, tN) = mkHash n
        (_, naiveN) = naiveSearch wsN tN
        (_, combNodesN, rbHN, clN) = combinedSearch wsN tN gs
        saveN = if naiveN == 0 then 0
                else (1 - fromIntegral combNodesN / fromIntegral naiveN) * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 12 (show naiveN)
      ++ padR 12 (show combNodesN)
      ++ padR 10 (show rbHN)
      ++ padR 10 (show clN)
      ++ padR 10 (showF 1 saveN ++ "%")
    ) [8, 10, 12, 14, 16]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: Clause growth rate — the key diagnostic
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. CLAUSE GROWTH: learned facts vs n ==="
  putStrLn "   (polynomial clauses → knowledge grows fast enough)"
  putStrLn "   (exponential clauses → learning can't keep up)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "2^n" ++ padR 12 "nodes"
    ++ padR 12 "clauses" ++ padR 12 "cl/2^n" ++ padR 12 "cl/n^2"
  putStrLn (replicate 64 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHash n
        (_, cs) = cdclSearch ws t
        twoN = (2::Int)^n
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show twoN)
      ++ padR 12 (show (csNodes cs))
      ++ padR 12 (show (csLearned cs))
      ++ padR 12 (showF 4 (fromIntegral (csLearned cs) / fromIntegral twoN :: Double))
      ++ padR 12 (showF 1 (fromIntegral (csLearned cs) / fromIntegral (n*n) :: Double))
    ) [8, 10, 12, 14, 16, 18]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "VERDICT:"
  putStrLn " clauses/n² → constant: learning is polynomial → hope!"
  putStrLn " clauses/2^n → constant: learning is exponential → same wall"
  putStrLn ""
  putStrLn " The wall's answers either contain enough info to collapse the"
  putStrLn " search (P=NP) or they're cryptographically uninformative (P≠NP)."
  putStrLn " This experiment measures which one it is."
  putStrLn "═══════════════════════════════════════════════════════════════════"
