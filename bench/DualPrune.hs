module Main where

{-
  THE DUAL QUESTION: instead of "which sums are reachable?",
  ask "which weights are FORCED IN or FORCED OUT?"

  If we can determine that w_i MUST be in every solution (or can NEVER be),
  we fix that bit and reduce n. If we fix enough bits in poly time,
  the residual problem becomes trivial.

  Forcing rules (polynomial-time deductions):

  1. BOUNDS:
     - w_i > T  →  FORCE OUT (too heavy alone)
     - sum_others < T  →  FORCE IN (need every weight including this one)
     - sum_others < T - w_i is impossible → if removing w_i makes T unreachable
       by bounds alone, FORCE IN

  2. MODULAR:
     - If w_i is the ONLY weight ≡ r (mod p) and T requires residue r
       from this weight → FORCE IN
     - If including w_i makes T mod p impossible → FORCE OUT

  3. PARITY:
     - T is odd and w_i is the only odd weight → FORCE IN
     - All weights even but T odd → NO SOLUTION

  4. INTERVAL:
     - After fixing some bits, recompute bounds on remaining sum
     - Tighten the window [lo, hi] for each unfixed weight

  5. RECURSIVE:
     - After fixing bits, re-apply all rules to the reduced instance
     - Fixed-point iteration until no more deductions

  KEY QUESTION: how many bits can we fix as a function of n?
    - O(n) fixed → problem collapses to O(1), POLYNOMIAL!
    - O(1) fixed → no help, still exponential
    - O(√n) fixed → reduces exponent but still exponential
-}

import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as Set
import Data.List (foldl', sortBy, partition)
import Data.Ord (comparing, Down(..))
import Data.Bits (xor, shiftR)
import PeqNP.ActorSolver (padR)

data Decision = ForcedIn | ForcedOut | Unknown
  deriving (Show, Eq)

data ReducedInstance = RI
  { riFixed    :: IM.IntMap Decision  -- index → decision
  , riUnfixed  :: [Int]              -- indices still unknown
  , riWeights  :: [Int]              -- original weights (indexed)
  , riTarget   :: Int                -- remaining target after forced-in
  , riForcedIn :: Int                -- count forced in
  , riForcedOut:: Int                -- count forced out
  } deriving (Show)

-- | Initialize: all weights unknown
initRI :: [Int] -> Int -> ReducedInstance
initRI ws t = RI
  { riFixed    = IM.empty
  , riUnfixed  = [0..length ws - 1]
  , riWeights  = ws
  , riTarget   = t
  , riForcedIn = 0
  , riForcedOut= 0
  }

-- | Force a weight IN: reduce target, remove from unfixed
forceIn :: ReducedInstance -> Int -> ReducedInstance
forceIn ri idx =
  let w = riWeights ri !! idx
  in ri { riFixed    = IM.insert idx ForcedIn (riFixed ri)
        , riUnfixed  = filter (/= idx) (riUnfixed ri)
        , riTarget   = riTarget ri - w
        , riForcedIn = riForcedIn ri + 1
        }

-- | Force a weight OUT: remove from unfixed
forceOut :: ReducedInstance -> Int -> ReducedInstance
forceOut ri idx =
  ri { riFixed     = IM.insert idx ForcedOut (riFixed ri)
     , riUnfixed   = filter (/= idx) (riUnfixed ri)
     , riForcedOut = riForcedOut ri + 1
     }

-- | Get unfixed weights with their indices
unfixedWeights :: ReducedInstance -> [(Int, Int)]  -- (index, weight)
unfixedWeights ri = [(i, riWeights ri !! i) | i <- riUnfixed ri]

-- | Sum of unfixed weights
unfixedSum :: ReducedInstance -> Int
unfixedSum ri = sum [riWeights ri !! i | i <- riUnfixed ri]

-- | Rule 1: BOUNDS
--   w_i > remaining target → FORCE OUT
--   sum_others < remaining target → FORCE IN
applyBounds :: ReducedInstance -> ReducedInstance
applyBounds ri =
  let t = riTarget ri
      uws = unfixedWeights ri
      totalUnfixed = sum (map snd uws)
  in foldl' (\acc (idx, w) ->
    if IM.member idx (riFixed acc) then acc  -- already decided
    else if w > riTarget acc then forceOut acc idx              -- too heavy
    else if totalUnfixed - w < riTarget acc then forceIn acc idx -- must include
    else acc
    ) ri uws

-- | Rule 2: MODULAR (check small primes)
applyModular :: [Int] -> ReducedInstance -> ReducedInstance
applyModular primes ri =
  foldl' (\acc p ->
    let t = riTarget acc
        uws = unfixedWeights acc
        -- Group unfixed weights by residue mod p
        residueGroups = IM.fromListWith (++) [(w `mod` p, [idx]) | (idx, w) <- uws]
        -- What residue does the target need?
        targetRes = t `mod` p
        -- For each weight: if it's the SOLE contributor of its residue class
        -- and that residue is needed, it might be forced
    in foldl' (\acc2 (idx, w) ->
      if IM.member idx (riFixed acc2) then acc2
      else
        let wRes = w `mod` p
            -- If we remove w, can the remaining unfixed weights produce targetRes mod p?
            -- Quick check: compute reachable residues without w
            othersRes = [w' `mod` p | (i, w') <- unfixedWeights acc2, i /= idx]
            -- DP mod p for "others" — O(n·p)
            reachableWithout = foldl' (\s r ->
              IS.union s (IS.map (\x -> (x + r) `mod` p) s)
              ) (IS.singleton 0) othersRes
            neededFromOthers = (targetRes - wRes) `mod` p
            neededWithout = targetRes `mod` p
        in if not (IS.member neededWithout reachableWithout)
              && IS.member neededFromOthers reachableWithout
           then forceIn acc2 idx    -- without w, can't reach target mod p; with w, can
           else if not (IS.member neededFromOthers reachableWithout)
                   && not (IS.member neededWithout reachableWithout)
           then acc2  -- hopeless either way (might be NO instance)
           else acc2
      ) acc uws
    ) ri primes

-- | Rule 3: PARITY
applyParity :: ReducedInstance -> ReducedInstance
applyParity ri =
  let t = riTarget ri
      uws = unfixedWeights ri
      oddWeights = filter (\(_, w) -> odd w) uws
  in if even t then ri  -- even target: parity doesn't force
     else case oddWeights of
       [(idx, _)] -> forceIn ri idx  -- sole odd weight, odd target → must include
       _ -> ri

-- | Rule 4: TIGHT INTERVAL — after fixing, check if each unfixed weight
-- is forced by the new bounds
applyTightInterval :: ReducedInstance -> ReducedInstance
applyTightInterval ri =
  let t = riTarget ri
      uws = unfixedWeights ri
      totalU = sum (map snd uws)
  in if t < 0 || t > totalU then ri  -- infeasible, nothing to fix
     else foldl' (\acc (idx, w) ->
       if IM.member idx (riFixed acc) then acc
       else
         let others = sum [w' | (i, w') <- unfixedWeights acc, i /= idx]
             tAcc = riTarget acc
         in if tAcc - w < 0              -- including w overshoots → OUT
            then forceOut acc idx
            else if others < tAcc         -- without w can't reach → IN
            then forceIn acc idx
            else if tAcc - w > others     -- including w requires more than remaining
            then forceOut acc idx
            else acc
       ) ri uws

-- | Fixed-point iteration: apply all rules until no more deductions
fixedPoint :: [Int] -> ReducedInstance -> (ReducedInstance, Int)  -- (result, iterations)
fixedPoint primes ri = go ri 0
  where
    go current iter =
      let step1 = applyBounds current
          step2 = applyParity step1
          step3 = applyTightInterval step2
          step4 = applyModular primes step3
          newFixed = IM.size (riFixed step4)
          oldFixed = IM.size (riFixed current)
      in if newFixed == oldFixed
         then (step4, iter + 1)
         else go step4 (iter + 1)

-- | Full DP reachable (ground truth)
dpReachable :: [Int] -> Int -> Bool
dpReachable ws t = Set.member t $
  foldl' (\acc w -> Set.union acc (Set.map (+w) acc)) (Set.singleton 0) ws

-- | After fixing, verify the reduced problem is correct
verifyReduction :: ReducedInstance -> Bool
verifyReduction ri =
  let unfixed = [riWeights ri !! i | i <- riUnfixed ri]
  in dpReachable unfixed (riTarget ri)

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

-- Dense instance: small weights relative to n
mkDense :: Int -> ([Int], Int)
mkDense n =
  let mix x0 = let x1 = (x0 `xor` (x0 `shiftR` 16)) * 0x45d9f3b
                   x2 = (x1 `xor` (x1 `shiftR` 16)) * 0x45d9f3b
               in x2 `xor` (x2 `shiftR` 16)
      ws = [1 + abs (mix (i * 2654435761 + 0x517cc1b7)) `mod` n
           | i <- [0..n-1 :: Int]]
      t  = sum ws `div` 2 + 1
  in (ws, t)

showF :: Int -> Double -> String
showF decimals x =
  let factor = 10 ^ decimals :: Int
      rounded = fromIntegral (round (x * fromIntegral factor) :: Int)
                / fromIntegral factor :: Double
  in show rounded

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn " THE DUAL PRUNE: don't enumerate sums — eliminate weights"
  putStrLn " \"Which weights are FORCED IN or FORCED OUT?\""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  let primes = [3, 5, 7, 11, 13]

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: How many bits can we fix? (density-1, NO instances)
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. DENSITY-1 (hard): how many weights can we fix? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 8 "type" ++ padR 10 "fixed-in"
    ++ padR 10 "fix-out" ++ padR 10 "unknown" ++ padR 10 "fix%"
    ++ padR 8 "iters"
  putStrLn (replicate 62 '-')
  mapM_ (\n -> do
    -- NO instance
    let (wsN, tN) = mkHash n
        riN = initRI wsN tN
        (resultN, itersN) = fixedPoint primes riN
        fixedN = riForcedIn resultN + riForcedOut resultN
        pctN = fromIntegral fixedN / fromIntegral n * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 8 "NO"
      ++ padR 10 (show (riForcedIn resultN))
      ++ padR 10 (show (riForcedOut resultN))
      ++ padR 10 (show (length (riUnfixed resultN)))
      ++ padR 10 (showF 1 pctN ++ "%")
      ++ padR 8 (show itersN)
    -- YES instance
    let (wsY, tY) = mkHashYes n
        riY = initRI wsY tY
        (resultY, itersY) = fixedPoint primes riY
        fixedY = riForcedIn resultY + riForcedOut resultY
        pctY = fromIntegral fixedY / fromIntegral n * 100 :: Double
    putStrLn $ padR 5 (show n) ++ padR 8 "YES"
      ++ padR 10 (show (riForcedIn resultY))
      ++ padR 10 (show (riForcedOut resultY))
      ++ padR 10 (show (length (riUnfixed resultY)))
      ++ padR 10 (showF 1 pctY ++ "%")
      ++ padR 8 (show itersY)
    ) [8, 10, 12, 14, 16, 18, 20, 24, 30]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Dense instances (easier) — does dual prune help more?
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. DENSE INSTANCES (weights ≈ n): more fixable? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "fixed-in" ++ padR 10 "fix-out"
    ++ padR 10 "unknown" ++ padR 10 "fix%" ++ padR 10 "density"
  putStrLn (replicate 55 '-')
  mapM_ (\n -> do
    let (ws, t) = mkDense n
        ri = initRI ws t
        (result, _) = fixedPoint primes ri
        fixed = riForcedIn result + riForcedOut result
        pct = fromIntegral fixed / fromIntegral n * 100 :: Double
        density = fromIntegral n / (logBase 2 (fromIntegral (maximum ws)) :: Double)
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show (riForcedIn result))
      ++ padR 10 (show (riForcedOut result))
      ++ padR 10 (show (length (riUnfixed result)))
      ++ padR 10 (showF 1 pct ++ "%")
      ++ padR 10 (showF 2 density)
    ) [10, 20, 30, 50, 80, 100]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Which rules contribute? (ablation study)
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. ABLATION: which rules fix the most bits? ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 12 "bounds" ++ padR 12 "parity"
    ++ padR 12 "interval" ++ padR 12 "modular" ++ padR 12 "ALL"
  putStrLn (replicate 65 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
        ri = initRI ws t
        -- Bounds only
        b = applyBounds ri
        bFixed = riForcedIn b + riForcedOut b
        -- Parity only
        p = applyParity ri
        pFixed = riForcedIn p + riForcedOut p
        -- Interval only
        i = applyTightInterval ri
        iFixed = riForcedIn i + riForcedOut i
        -- Modular only
        m = applyModular primes ri
        mFixed = riForcedIn m + riForcedOut m
        -- All combined (fixed point)
        (allR, _) = fixedPoint primes ri
        allFixed = riForcedIn allR + riForcedOut allR
    putStrLn $ padR 5 (show n)
      ++ padR 12 (show bFixed)
      ++ padR 12 (show pFixed)
      ++ padR 12 (show iFixed)
      ++ padR 12 (show mFixed)
      ++ padR 12 (show allFixed)
    ) [8, 10, 12, 14, 16, 20]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: The scaling question
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. SCALING: fixed% vs n (density-1) ==="
  putStrLn "   Does fix% grow (→poly), stay flat (→speedup), or shrink (→futile)?"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 10 "fixed" ++ padR 10 "unknown"
    ++ padR 10 "fix%" ++ padR 14 "remaining-2^k" ++ padR 10 "full-2^n"
  putStrLn (replicate 60 '-')
  mapM_ (\n -> do
    let (ws, t) = mkHashYes n
        ri = initRI ws t
        (result, _) = fixedPoint primes ri
        fixed = riForcedIn result + riForcedOut result
        unknown = length (riUnfixed result)
        pct = fromIntegral fixed / fromIntegral n * 100 :: Double
        remaining = (2::Integer)^unknown
        full = (2::Integer)^n
    putStrLn $ padR 5 (show n)
      ++ padR 10 (show fixed)
      ++ padR 10 (show unknown)
      ++ padR 10 (showF 1 pct ++ "%")
      ++ padR 14 (show remaining)
      ++ padR 10 (show full)
    ) [8, 10, 12, 14, 16, 18, 20, 24, 30]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: Correctness check
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. CORRECTNESS: does fixing preserve the answer? ==="
  putStrLn ""
  mapM_ (\n -> do
    let (wsY, tY) = mkHashYes n
        riY = initRI wsY tY
        (resultY, _) = fixedPoint primes riY
        correctY = verifyReduction resultY
    let (wsN, tN) = mkHash n
        riN = initRI wsN tN
        (resultN, _) = fixedPoint primes riN
        correctN = not (dpReachable [riWeights resultN !! i | i <- riUnfixed resultN] (riTarget resultN))
    putStrLn $ "  n=" ++ show n
      ++ " YES-instance reduced: " ++ show (length (riUnfixed resultY))
      ++ " unknown, correct=" ++ show correctY
      ++ " | NO-instance reduced: " ++ show (length (riUnfixed resultN))
      ++ " unknown, correct=" ++ show correctN
    ) [8, 10, 12]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "VERDICT:"
  putStrLn " fix% → 100% as n grows  →  DUAL PRUNE SOLVES IT (poly time!)"
  putStrLn " fix% → constant k%      →  reduces exponent by k%, still exp"
  putStrLn " fix% → 0% as n grows    →  dual prune useless for density-1"
  putStrLn ""
  putStrLn "The dream: fix O(n - polylog(n)) bits → residual is polylog(n) → trivial"
  putStrLn "The nightmare: fix O(1) bits → residual is n - O(1) → unchanged"
  putStrLn "═══════════════════════════════════════════════════════════════════"
