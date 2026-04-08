module PeqNP.Impossibility
  ( MinSizeResult(..)
  , minDistinguishingModulus
  , distinctReachableSums
  , ScalingDataPoint(..)
  , scalingAnalysis
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.List (find)
import PeqNP.DPSolver (dpTable)

-- | Result of searching for the minimum modulus that preserves the answer
data MinSizeResult = MinSizeResult
  { msrDistinctSums   :: Int        -- ^ Number of distinct reachable sums
  , msrTargetReachable :: Bool
  , msrMinModulus      :: Maybe Int  -- ^ Smallest k where ZMod k works, Nothing if not found
  } deriving (Show)

-- | Count distinct reachable sums for a Subset Sum instance
distinctReachableSums :: [Int] -> Int
distinctReachableSums = Map.size . dpTable

-- | Find the minimum k such that ZMod k with SOME generator
-- preserves the answer for this instance.
--
-- For a NO instance with target T and reachable sums S:
-- ZMod k works iff there exists some g in Z/kZ such that
-- (T*g) mod k ∉ { (s*g) mod k | s ∈ S }
--
-- Since the canonical homomorphism uses g=1:
-- h(n) = n mod k, so we need: T mod k ∉ { s mod k | s ∈ S }
--
-- We search k = 2, 3, ... up to a bound.
minDistinguishingModulus :: [Int] -> Int -> Int -> MinSizeResult
minDistinguishingModulus elems target maxK =
  let table = dpTable elems
      reachable = Set.fromList (Map.keys table)
      hasSolution = Set.member target reachable
      numDistinct = Set.size reachable
  in if hasSolution
     then MinSizeResult numDistinct True (Just 1)
     else
       let tryK k =
             let targetMod = target `mod` k
                 reachableMods = Set.map (`mod` k) reachable
             in not (Set.member targetMod reachableMods)
       in MinSizeResult numDistinct False (find tryK [2..maxK])

-- | A single data point in the scaling analysis
data ScalingDataPoint = SDP
  { sdpN          :: Int
  , sdpElements   :: [Int]
  , sdpTarget     :: Int
  , sdpDistinct   :: Int
  , sdpMinK       :: Maybe Int
  } deriving (Show)

-- | Run the scaling analysis: for given instances of increasing size,
-- compute the minimum modulus needed.
--
-- THE KEY EXPERIMENT:
-- If minK grows polynomially with n → evidence for P = NP
-- If minK grows exponentially with n → evidence for P ≠ NP
scalingAnalysis :: [([Int], Int)] -> Int -> [ScalingDataPoint]
scalingAnalysis instances maxK =
  [ let result = minDistinguishingModulus elems target maxK
    in SDP
      { sdpN        = length elems
      , sdpElements = elems
      , sdpTarget   = target
      , sdpDistinct = msrDistinctSums result
      , sdpMinK     = msrMinModulus result
      }
  | (elems, target) <- instances
  ]
