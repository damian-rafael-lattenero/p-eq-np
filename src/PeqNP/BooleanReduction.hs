module PeqNP.BooleanReduction
  ( -- * Boolean formula types (inspired by mlabs-test PLSentence)
    BoolFormula(..)
  , evaluate
    -- * Subset Sum as Boolean Satisfiability
  , subsetSumToSAT
  , satToSubsetSum
    -- * The categorical connection
  , decisionPathToAssignment
  , assignmentToDecisionPath
  , showReduction
  ) where

import PeqNP.BruteForce (Decision(..), Path)

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.List (intercalate)

-- | Boolean formulas — simplified version of mlabs-test's PLSentence.
--
-- In mlabs-test:
--   PLSentence → NORSentence was a FUNCTOR preserving evaluation.
--   optimizePls was a QUOTIENTING ENDOFUNCTOR reducing formula size.
--
-- Here we use the same pattern: Subset Sum → SAT is a functor
-- from the enriched decision category to the boolean satisfiability category.
-- Both are NP-complete, so the functor is structure-preserving.
data BoolFormula
  = Var Int              -- ^ Variable x_i (True = include element i)
  | Not BoolFormula
  | And BoolFormula BoolFormula
  | Or  BoolFormula BoolFormula
  deriving (Eq)

instance Show BoolFormula where
  showsPrec _ (Var i) = showString ("x" ++ show i)
  showsPrec p (Not f) = showParen (p > 9) $ showString "!" . showsPrec 10 f
  showsPrec p (And a b) = showParen (p > 3) $ showsPrec 4 a . showString " & " . showsPrec 4 b
  showsPrec p (Or a b) = showParen (p > 2) $ showsPrec 3 a . showString " | " . showsPrec 3 b

-- | Evaluate a boolean formula under an assignment
evaluate :: Map Int Bool -> BoolFormula -> Bool
evaluate env (Var i)   = Map.findWithDefault False i env
evaluate env (Not f)   = not (evaluate env f)
evaluate env (And a b) = evaluate env a && evaluate env b
evaluate env (Or a b)  = evaluate env a || evaluate env b

-- ═══════════════════════════════════════════════════════════
-- Subset Sum ↔ SAT reduction
-- ═══════════════════════════════════════════════════════════

-- | Encode Subset Sum as a Boolean Satisfiability instance.
--
-- Given elements [w1, ..., wn] and target T:
-- Variable x_i means "include element i".
-- The formula encodes: "the sum of selected elements equals T".
--
-- This is a direct encoding using bit-level addition.
-- For simplicity we use the "counting" approach:
-- enumerate all subsets that sum to T and OR them together.
-- (This is exponential in the formula, but demonstrates the reduction.)
--
-- THE CATEGORICAL INSIGHT:
-- Just as mlabs-test's toNOR transforms PLSentence → NORSentence
-- (functor between formula categories preserving evaluation),
-- subsetSumToSAT transforms a decision-category problem into a
-- boolean-category problem, preserving the answer.
subsetSumToSAT :: [Int] -> Int -> BoolFormula
subsetSumToSAT elems target =
  case validSubsets of
    []     -> And (Var 0) (Not (Var 0))  -- unsatisfiable
    [s]    -> s
    (s:ss) -> foldl Or s ss
  where
    n = length elems
    -- Generate all 2^n assignments, keep those summing to target
    validSubsets = [ assignmentFormula mask
                   | mask <- allMasks n
                   , sum [w | (w, True) <- zip elems mask] == target
                   ]
    -- For a given mask [True, False, True, ...]:
    -- produce  (x1 & !x2 & x3 & ...)
    assignmentFormula mask =
      case [ if b then Var i else Not (Var i)
           | (i, b) <- zip [0..] mask
           ] of
        []     -> Or (Var 0) (Not (Var 0))  -- tautology (empty subset)
        [x]    -> x
        (x:xs) -> foldl And x xs

-- | Convert a SAT solution back to a Subset Sum solution.
-- Given an assignment (Map Int Bool) and the elements list,
-- return the included elements.
satToSubsetSum :: [Int] -> Map Int Bool -> [Int]
satToSubsetSum elems assignment =
  [ w | (i, w) <- zip [0..] elems
      , Map.findWithDefault False i assignment
  ]

-- | Convert a decision path to a boolean assignment.
-- Include x_i → x_i = True, Skip x_i → x_i = False
decisionPathToAssignment :: Path -> Map Int Bool
decisionPathToAssignment path =
  Map.fromList $ zip [0..] (map isInclude path)
  where
    isInclude (Include _) = True
    isInclude (Skip _)    = False

-- | Convert a boolean assignment back to a decision path
assignmentToDecisionPath :: [Int] -> Map Int Bool -> Path
assignmentToDecisionPath elems assignment =
  [ if Map.findWithDefault False i assignment
    then Include w
    else Skip w
  | (i, w) <- zip [0..] elems
  ]

-- ═══════════════════════════════════════════════════════════
-- Display
-- ═══════════════════════════════════════════════════════════

allMasks :: Int -> [[Bool]]
allMasks 0 = [[]]
allMasks n = [b : rest | b <- [True, False], rest <- allMasks (n - 1)]

-- | Show the reduction as a formatted string
showReduction :: [Int] -> Int -> String
showReduction elems target = unlines
  [ "  Subset Sum: elements = " ++ show elems ++ ", target = " ++ show target
  , "  Variables:  " ++ intercalate ", " ["x" ++ show i ++ "=" ++ show w | (i, w) <- zip [(0::Int)..] elems]
  , "  SAT formula (DNF):"
  , "    " ++ show (subsetSumToSAT elems target)
  ]
