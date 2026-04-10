module Main where

{-
  PERSISTENT HOMOLOGY: Topological Data Analysis for Subset Sum

  Completely outside the algebraic paradigm. View achievable subset sums
  as a 1D point cloud. As connectivity radius ε grows from 0 to max,
  components merge — producing a persistence diagram.

  For 1D point clouds: persistence diagram = sorted gap distribution
  between consecutive sums. No union-find needed.

  KEY QUESTION: does the persistence diagram carry a poly-time readable
  signal that distinguishes YES instances from NO instances?

  Five experiments:
    1. Persistence diagram: H0 for small n, YES vs NO
    2. Gap distribution: histogram of consecutive distances
    3. Component count: #components at various ε scales
    4. Topological signal: is the gap containing T anomalous?
    5. Scalability: can we estimate persistence from k-smooth samples?
-}

import qualified Data.Set as Set
import qualified Data.IntSet as IS
import Data.List (foldl', sort, group, sortBy, genericLength)
import Data.Bits (xor, shiftR, (.|.), bit, zeroBits)
import PeqNP.ActorSolver (padR)

-- | All achievable subset sums, sorted
allSortedSums :: [Int] -> [Int]
allSortedSums ws = Set.toAscList $
  foldl' (\acc w -> Set.union acc (Set.map (+w) acc)) (Set.singleton 0) ws

-- | Consecutive gaps (= H0 persistence diagram for 1D)
gapDistribution :: [Int] -> [Int]
gapDistribution xs = sort $ zipWith (-) (drop 1 xs) xs

-- | Gap stats: mean, stddev, min, max, median
gapStats :: [Int] -> (Double, Double, Int, Int, Int)
gapStats [] = (0, 0, 0, 0, 0)
gapStats gs =
  let n = length gs
      mean = fromIntegral (sum gs) / fromIntegral n :: Double
      var  = sum [let d = fromIntegral g - mean in d*d | g <- gs] / fromIntegral n
      sorted = sort gs
  in (mean, sqrt var, minimum gs, maximum gs, sorted !! (n `div` 2))

-- | Number of components at scale ε
-- Each gap > ε contributes a "break" between components
componentCountAt :: [Int] -> Int -> Int
componentCountAt gaps eps = 1 + length (filter (> eps) gaps)

-- | Info about the gap containing target T
-- Returns: (gap_size, gap_rank_from_top, is_reachable)
targetGapInfo :: [Int] -> Int -> (Int, Int, Bool)
targetGapInfo sortedSums target
  | Set.member target (Set.fromList sortedSums) = (0, 0, True)
  | otherwise =
    let -- Find the gap T falls into
        below = filter (< target) sortedSums
        above = filter (> target) sortedSums
    in if null below || null above then (0, 0, False)
       else let lo = maximum below
                hi = minimum above
                gapSize = hi - lo
                allGaps = sort $ zipWith (-) (drop 1 sortedSums) sortedSums
                rank = length (filter (>= gapSize) allGaps)
            in (gapSize, rank, False)

-- | k-smooth sums: all subsets of size ≤ k
kSmoothSums :: [Int] -> Int -> [Int]
kSmoothSums weights maxK =
  let n = length weights
      go idx mask val size acc
        | size > maxK = acc
        | idx >= n    = if size > 0 then Set.insert val acc else acc
        | otherwise   =
            let acc1 = go (idx + 1) mask val size acc
                acc2 = go (idx + 1) (mask .|. bit idx)
                          (val + weights !! idx) (size + 1) acc1
            in if size > 0 then Set.insert val acc2 else acc2
  in Set.toAscList $ Set.insert 0 $ go 0 (zeroBits :: Int) 0 0 Set.empty

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
  putStrLn " PERSISTENT HOMOLOGY: TDA for Subset Sum"
  putStrLn " The shape of the reachable-sum point cloud"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 1: Persistence diagram (gap stats) for YES vs NO
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 1. H0 PERSISTENCE: gap statistics, YES vs NO ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 8 "#sums"
    ++ padR 10 "max_gap" ++ padR 10 "mean" ++ padR 10 "stddev"
    ++ padR 10 "median"
  putStrLn (replicate 60 '-')
  mapM_ (\n -> do
    let (wsN, _) = mkHash n
        sumsN = allSortedSums wsN
        gapsN = gapDistribution sumsN
        (meanN, stdN, _, maxN, medN) = gapStats gapsN
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 8 (show (length sumsN))
      ++ padR 10 (show maxN)
      ++ padR 10 (showF 1 meanN)
      ++ padR 10 (showF 1 stdN)
      ++ padR 10 (show medN)
    let (wsY, _) = mkHashYes n
        sumsY = allSortedSums wsY
        gapsY = gapDistribution sumsY
        (meanY, stdY, _, maxY, medY) = gapStats gapsY
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 8 (show (length sumsY))
      ++ padR 10 (show maxY)
      ++ padR 10 (showF 1 meanY)
      ++ padR 10 (showF 1 stdY)
      ++ padR 10 (show medY)
    ) [6, 8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 2: Gap distribution — first 15 gaps
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 2. GAP DISTRIBUTION: smallest 15 gaps (n=10) ==="
  putStrLn ""
  let (ws2N, _) = mkHash 10
      gaps2N = gapDistribution (allSortedSums ws2N)
  let (ws2Y, _) = mkHashYes 10
      gaps2Y = gapDistribution (allSortedSums ws2Y)
  putStrLn $ "  NO:  " ++ show (take 15 gaps2N)
  putStrLn $ "  YES: " ++ show (take 15 gaps2Y)
  putStrLn ""
  putStrLn "  Largest 10 gaps (persistence features):"
  putStrLn $ "  NO:  " ++ show (take 10 (reverse (sort gaps2N)))
  putStrLn $ "  YES: " ++ show (take 10 (reverse (sort gaps2Y)))
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 3: Component count sweep
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 3. COMPONENT COUNT: #components at various ε (n=12) ==="
  putStrLn ""
  let (ws3, _) = mkHash 12
      sums3 = allSortedSums ws3
      gaps3 = zipWith (-) (drop 1 sums3) sums3
      maxG3 = if null gaps3 then 1 else maximum gaps3
      epsilons = [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512,
                  maxG3 `div` 4, maxG3 `div` 2, maxG3]
  putStrLn $ padR 10 "epsilon" ++ padR 12 "#components" ++ padR 12 "merged%"
  putStrLn (replicate 34 '-')
  let totalComps = length sums3
  mapM_ (\eps -> do
    let comps = componentCountAt gaps3 eps
        merged = (1 - fromIntegral comps / fromIntegral totalComps) * 100 :: Double
    putStrLn $ padR 10 (show eps) ++ padR 12 (show comps)
      ++ padR 12 (showF 1 merged ++ "%")
    ) (sort (IS.toList (IS.fromList epsilons)))
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 4: THE CRUX — topological signal at target
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 4. TOPOLOGICAL SIGNAL: is the gap at T special? ==="
  putStrLn "   score = gap_at_T / mean_gap  (score ≈ 1 → no signal)"
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 6 "inst" ++ padR 10 "gap_at_T"
    ++ padR 10 "mean_gap" ++ padR 10 "score" ++ padR 8 "rank"
    ++ padR 8 "#gaps"
  putStrLn (replicate 58 '-')
  mapM_ (\n -> do
    -- NO instance
    let (wsN, tN) = mkHash n
        sumsN = allSortedSums wsN
        gapsN = gapDistribution sumsN
        (meanN, _, _, _, _) = gapStats gapsN
        (gapN, rankN, _) = targetGapInfo sumsN tN
        scoreN = if meanN == 0 then 0 else fromIntegral gapN / meanN :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "NO"
      ++ padR 10 (show gapN)
      ++ padR 10 (showF 1 meanN)
      ++ padR 10 (showF 2 scoreN)
      ++ padR 8 (show rankN)
      ++ padR 8 (show (length gapsN))
    -- YES instance
    let (wsY, tY) = mkHashYes n
        sumsY = allSortedSums wsY
        gapsY = gapDistribution sumsY
        (meanY, _, _, _, _) = gapStats gapsY
        (gapY, rankY, reachY) = targetGapInfo sumsY tY
        scoreY = if reachY then 0 else
                 if meanY == 0 then 0 else fromIntegral gapY / meanY :: Double
    putStrLn $ padR 5 (show n) ++ padR 6 "YES"
      ++ padR 10 (if reachY then "0 (IN)" else show gapY)
      ++ padR 10 (showF 1 meanY)
      ++ padR 10 (if reachY then "0.0" else showF 2 scoreY)
      ++ padR 8 (show rankY)
      ++ padR 8 (show (length gapsY))
    ) [6, 8, 10, 12]
  putStrLn ""

  -- ─────────────────────────────────────────────────────────────
  -- Section 5: Polynomial approximation via k-smooth
  -- ─────────────────────────────────────────────────────────────
  putStrLn "=== 5. POLYNOMIAL PERSISTENCE: k-smooth approximation ==="
  putStrLn ""
  putStrLn $ padR 5 "n" ++ padR 5 "k" ++ padR 10 "#smooth"
    ++ padR 10 "#exact" ++ padR 12 "max_gap_sm" ++ padR 12 "max_gap_ex"
    ++ padR 10 "ratio"
  putStrLn (replicate 65 '-')
  mapM_ (\n -> do
    let (ws, _) = mkHash n
        exact = allSortedSums ws
        gapsEx = gapDistribution exact
        maxEx = if null gapsEx then 0 else maximum gapsEx
    mapM_ (\k -> do
      let smooth = kSmoothSums ws k
          gapsSm = gapDistribution smooth
          maxSm = if null gapsSm then 0 else maximum gapsSm
          ratio = if maxEx == 0 then 0
                  else fromIntegral maxSm / fromIntegral maxEx :: Double
      putStrLn $ padR 5 (show n) ++ padR 5 (show k)
        ++ padR 10 (show (length smooth))
        ++ padR 10 (show (length exact))
        ++ padR 12 (show maxSm)
        ++ padR 12 (show maxEx)
        ++ padR 10 (showF 2 ratio)
      ) [2, 3, 4]
    ) [8, 10, 12]
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "ANALYSIS:"
  putStrLn " For 1D point clouds, H0 persistence = gap distribution."
  putStrLn " Section 4 is decisive:"
  putStrLn "   score ≈ 1 for NO → gap at T is typical → no topological signal"
  putStrLn "   score >> 1 for NO → gap at T is anomalous → potential signal!"
  putStrLn "   score = 0 for YES → T is in the point cloud (trivially)"
  putStrLn ""
  putStrLn " If score ≈ 1: topology confirms the exponential wall."
  putStrLn " The sum cloud's shape is determined by weights, not by T."
  putStrLn " Knowing the shape doesn't tell you if one specific point is in it."
  putStrLn "═══════════════════════════════════════════════════════════════════"
