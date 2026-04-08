module PeqNP.NTT
  ( -- * Point evaluation
    evalProductAt
  , evalPolyAt
    -- * NTT-based coefficient extraction
  , nttCoeffAt
  , primitiveRoot
  , modPow
  ) where

-- | Evaluate the product g(x) = Π(1 + x^wᵢ) at a point α modulo p.
--
-- THIS IS O(n) — the key efficiency insight.
-- We don't need to expand the polynomial (O(2^n) terms).
-- We just compute Π(1 + α^wᵢ) mod p, one factor at a time.
evalProductAt :: Int -> Int -> [Int] -> Int
evalProductAt p alpha weights = foldl step 1 weights
  where
    step acc w = (acc * (1 + modPow p alpha w)) `mod` p

-- | Evaluate an arbitrary polynomial (given as coefficient list) at a point
evalPolyAt :: Int -> Int -> [(Int, Int)] -> Int
evalPolyAt p alpha terms = foldl step 0 terms `mod` p
  where
    step acc (e, c) = (acc + c * modPow p alpha e) `mod` p

-- | Extract coefficient of x^T from g(x) = Π(1 + x^wᵢ) using NTT.
--
-- Method: evaluate g at all q-th roots of unity ω^0, ω^1, ..., ω^(q-1)
-- where ω is a primitive q-th root of unity mod p (requires q | p-1).
-- Then the coefficient [x^T] g(x) mod p = (1/q) Σ g(ω^j) * ω^(-jT) mod p.
--
-- Total cost: O(n*q) for evaluations + O(q) for inverse DFT = O(n*q).
-- If q = poly(n) → polynomial time!
nttCoeffAt :: Int -> Int -> Int -> [Int] -> Maybe Int
nttCoeffAt p q target weights = do
  -- Need q | (p-1) for q-th roots of unity to exist in Z/pZ
  omega <- primitiveRoot p q
  let -- Evaluate g at all q-th roots of unity: g(ω^j) for j=0..q-1
      evals = [ evalProductAt p (modPow p omega j) weights | j <- [0..q-1] ]
      -- Inverse DFT: [x^T] = (1/q) Σ_j g(ω^j) * ω^(-jT)
      qInv = modInverse p q
      omegaInv = modPow p omega (p - 1 - 1)  -- ω^(-1) = ω^(p-2) if ω^(p-1)=1
      coeffT = sum [ (evals !! j) * modPow p (modPow p omegaInv j) target
                   | j <- [0..q-1]
                   ] `mod` p
  return ((coeffT * qInv) `mod` p)

-- | Find a primitive q-th root of unity modulo p.
-- Requires q | (p-1). Returns Nothing if none exists.
primitiveRoot :: Int -> Int -> Maybe Int
primitiveRoot p q
  | (p - 1) `mod` q /= 0 = Nothing
  | otherwise =
      -- A primitive q-th root is g^((p-1)/q) where g is a generator of Z/pZ*
      -- Try g = 2, 3, ... until we find one whose ((p-1)/q)-th power has order q
      let e = (p - 1) `div` q
          candidates = [ modPow p g e | g <- [2..p-1] ]
          isRoot omega = omega /= 0
                      && modPow p omega q == 1
                      && all (\d -> modPow p omega d /= 1) (properDivisors q)
      in case filter isRoot candidates of
           (omega:_) -> Just omega
           []        -> Nothing

-- | Modular exponentiation: a^n mod p (by repeated squaring)
modPow :: Int -> Int -> Int -> Int
modPow p base' expo
  | expo == 0 = 1
  | expo < 0  = modPow p (modInverse p base') (negate expo)
  | even expo = let half = modPow p base' (expo `div` 2)
                in (half * half) `mod` p
  | otherwise = (base' * modPow p base' (expo - 1)) `mod` p

-- | Modular inverse via Fermat's little theorem: a^(-1) = a^(p-2) mod p
modInverse :: Int -> Int -> Int
modInverse p a = modPow p a (p - 2)

-- | Proper divisors of n (divisors < n, > 0)
properDivisors :: Int -> [Int]
properDivisors n = [d | d <- [1..n-1], n `mod` d == 0]
