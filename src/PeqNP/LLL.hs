module PeqNP.LLL
  ( -- * Lattice construction
    subsetSumLattice
    -- * LLL reduction
  , lllReduce
    -- * Subset Sum solver via LLL
  , lllSolve
  , LLLResult(..)
  , showLLLResult
    -- * Density
  , density
  ) where

import Data.Ratio ((%))
import Data.List (minimumBy)
import Data.Ord (comparing)
import qualified Data.Set as Set

-- | Density of a Subset Sum instance: n / log2(max_weight)
density :: [Int] -> Double
density [] = 0
density elems =
  let n = length elems
      maxW = maximum elems
  in if maxW <= 1 then fromIntegral n
     else fromIntegral n / logBase 2 (fromIntegral maxW)

-- ═══════════════════════════════════════════════════════════
-- Lattice construction for Subset Sum
-- ═══════════════════════════════════════════════════════════

type Vec = [Rational]
type Lattice = [Vec]

-- | Construct the CJLOSS lattice for Subset Sum.
-- Given weights [w1..wn] and target T:
-- Build (n+1) × (n+1) matrix where the solution vector is short.
subsetSumLattice :: [Int] -> Int -> Lattice
subsetSumLattice elems target =
  let n = length elems
      bigN = ceiling (sqrt (fromIntegral n) :: Double)  -- scaling factor
      -- First n rows: identity with N*wi in last column
      weightRows = [ [if i == j then 1 else 0 | j <- [0..n-1]] ++ [fromIntegral bigN * fromIntegral (elems !! i)]
                    | i <- [0..n-1] ]
      -- Last row: zeros with N*T in last column
      targetRow = [0 | _ <- [0..n-1]] ++ [fromIntegral bigN * fromIntegral target]
  in weightRows ++ [targetRow]

-- ═══════════════════════════════════════════════════════════
-- LLL Algorithm (Lenstra-Lenstra-Lovász basis reduction)
-- ═══════════════════════════════════════════════════════════

-- | Gram-Schmidt orthogonalization (returns orthogonal basis + coefficients)
gramSchmidt :: Lattice -> (Lattice, [[Rational]])
gramSchmidt [] = ([], [])
gramSchmidt basis =
  let n = length basis
      (ortho, mu) = go 0 [] []
  in (ortho, mu)
  where
    go i ortho mu
      | i >= length basis = (reverse ortho, reverse mu)
      | otherwise =
          let bi = basis !! i
              -- Compute mu_ij = <bi, ortho_j> / <ortho_j, ortho_j>
              muRow = [ if denom == 0 then 0 else dotProd bi (ortho !! j) / denom
                      | j <- [0..i-1]
                      , let denom = dotProd (ortho !! j) (ortho !! j)
                      ]
              -- b*_i = b_i - Σ mu_ij * b*_j
              biStar = foldl (\acc (j, m) -> vecSub acc (vecScale m (ortho !! j)))
                             bi (zip [0..] muRow)
          in go (i+1) (biStar : ortho) (muRow : mu)

-- | LLL reduction with parameter delta (typically 3/4)
lllReduce :: Rational -> Lattice -> Lattice
lllReduce delta basis
  | length basis <= 1 = basis
  | otherwise = go basis 1
  where
    n = length basis

    go b k
      | k >= n = b
      | otherwise =
          let -- Size reduce b[k] against b[0..k-1]
              b' = sizeReduce b k
              (ortho, mu) = gramSchmidt b'
              -- Lovász condition: |b*_k|² ≥ (delta - mu²_{k,k-1}) * |b*_{k-1}|²
              muKK1 = if k-1 < length (mu !! k) then mu !! k !! (k-1) else 0
              normK = dotProd (ortho !! k) (ortho !! k)
              normK1 = dotProd (ortho !! (k-1)) (ortho !! (k-1))
          in if normK >= (delta - muKK1 * muKK1) * normK1
             then go b' (k + 1)  -- condition satisfied, move to next
             else
               -- Swap b[k] and b[k-1], go back
               let b'' = swapAt k (k-1) b'
               in go b'' (max 1 (k - 1))

    sizeReduce b k = foldl (reduceStep k) b (reverse [0..k-1])

    reduceStep k b j =
      let (_, mu) = gramSchmidt b
          m = if j < length (mu !! k) then mu !! k !! j else 0
          r = round m :: Integer
      in if r == 0 then b
         else replaceAt k (vecSub (b !! k) (vecScale (fromInteger r) (b !! j))) b

-- ═══════════════════════════════════════════════════════════
-- Solver
-- ═══════════════════════════════════════════════════════════

data LLLResult = LLLResult
  { llrFound     :: Bool
  , llrCorrect   :: Bool
  , llrSolution  :: Maybe [Int]
  , llrDensity   :: Double
  , llrBasisSize :: Int
  } deriving (Show)

-- | Solve Subset Sum via LLL lattice reduction.
lllSolve :: [Int] -> Int -> LLLResult
lllSolve elems target =
  let lattice = subsetSumLattice elems target
      reduced = lllReduce (3 % 4) lattice
      n = length elems
      d = density elems
      dpAnswer = Set.member target dpR
      dpR = foldl (\s w -> Set.union s (Set.map (+ w) s)) (Set.singleton 0) elems
      -- Look for a short vector that encodes a solution
      -- A solution vector has: first n entries ∈ {0,1}, last entry = 0
      solution = findSolution reduced n elems target
  in LLLResult
    { llrFound    = solution /= Nothing
    , llrCorrect  = (solution /= Nothing) == dpAnswer
    , llrSolution = solution
    , llrDensity  = d
    , llrBasisSize = length reduced
    }

findSolution :: Lattice -> Int -> [Int] -> Int -> Maybe [Int]
findSolution reduced n elems target =
  let candidates = [ vec | vec <- reduced
                   , length vec > n
                   , last vec == 0  -- last entry must be 0 (sum constraint met)
                   , all (\x -> x == 0 || x == 1) (take n vec)  -- binary
                   ]
      -- Also try negated vectors (LLL can find -v instead of v)
      negCandidates = [ map negate vec | vec <- reduced
                      , length vec > n
                      , last vec == 0
                      , all (\x -> x == 0 || x == -1) (take n vec)
                      ]
      allCands = candidates ++ map (map abs) negCandidates
      -- Check each candidate: does the selection sum to target?
      check vec =
        let selection = [elems !! i | i <- [0..n-1], take n vec !! i == 1]
        in sum selection == target
  in case filter check allCands of
       (v:_) -> Just [elems !! i | i <- [0..n-1], take n v !! i == 1]
       []    -> Nothing

-- ═══════════════════════════════════════════════════════════
-- Vector operations
-- ═══════════════════════════════════════════════════════════

dotProd :: Vec -> Vec -> Rational
dotProd a b = sum (zipWith (*) a b)

vecSub :: Vec -> Vec -> Vec
vecSub = zipWith (-)

vecScale :: Rational -> Vec -> Vec
vecScale s = map (* s)

swapAt :: Int -> Int -> [a] -> [a]
swapAt i j xs = [ if k == i then xs !! j else if k == j then xs !! i else xs !! k
                | k <- [0..length xs - 1] ]

replaceAt :: Int -> a -> [a] -> [a]
replaceAt i x xs = take i xs ++ [x] ++ drop (i+1) xs

showLLLResult :: LLLResult -> String
showLLLResult r = unlines
  [ "  Density:  " ++ show (roundTo 2 (llrDensity r))
  , "  Found:    " ++ show (llrFound r)
  , "  Correct:  " ++ show (llrCorrect r)
  , "  Solution: " ++ show (llrSolution r)
  ]
  where
    roundTo n x = fromIntegral (round (x * 10^(n::Int)) :: Int) / 10^(n::Int)
