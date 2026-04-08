module Main where

import Test.Tasty
import Test.Tasty.QuickCheck

import PeqNP.EnrichedCategory (EnrichedCategory(eid, (|.|)))
import PeqNP.EnrichedArrow (EnrichedArrow(..))
import PeqNP.Composition ((⊗), (⊕), composeAll)
import PeqNP.SubsetSum (Sum(..), DecisionState(..), include, skip, reachedTarget)
import PeqNP.BruteForce (allPaths, solveBruteForce, Decision(..), extractIncluded)
import PeqNP.DPSolver (solveDPAll)
import PeqNP.Comparison (compareApproaches, ComparisonResult(..))
import PeqNP.Quotient (quotientByMetadata, quotientSize, lookupTarget)
import PeqNP.Functor (EnrichedFunctor(..), applyFunctor, modularFunctor, identityFunctor)
import PeqNP.BooleanReduction (subsetSumToSAT, evaluate, decisionPathToAssignment)

import qualified Data.Map.Strict as Map

import Data.List (sort)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "P=NP Enriched Category"
  [ enrichedCategoryLaws
  , metadataAccumulation
  , bruteForceTests
  , dpComparisonTests
  , quotientFunctorTests
  , booleanReductionTests
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 1: EnrichedCategory laws
-- ═══════════════════════════════════════════════════════════

enrichedCategoryLaws :: TestTree
enrichedCategoryLaws = testGroup "EnrichedCategory laws"
  [ testProperty "left identity: eid |.| f has same metadata as f" $
      \n -> let f = include n
            in metadata (eid |.| f) === metadata f

  , testProperty "right identity: f |.| eid has same metadata as f" $
      \n -> let f = include n
            in metadata (f |.| eid) === metadata f

  , testProperty "associativity: (f |.| g) |.| h == f |.| (g |.| h) on metadata" $
      \(a, b, c) ->
        let f = include a
            g = include b
            h = include c
        in metadata ((f |.| g) |.| h) === metadata (f |.| (g |.| h))

  , testProperty "metadata homomorphism: metadata (f ⊕ g) == metadata f <> metadata g" $
      \(a, b) ->
        let f = include a
            g = include b
        in metadata (f ⊕ g) === metadata f <> metadata g
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 2: Metadata accumulation
-- ═══════════════════════════════════════════════════════════

metadataAccumulation :: TestTree
metadataAccumulation = testGroup "Metadata accumulation"
  [ testProperty "include x carries Sum x" $
      \x -> metadata (include x) === Sum x

  , testProperty "skip x carries Sum 0" $
      \x -> metadata (skip x) === Sum 0

  , testProperty "composeAll includes sums correctly" $
      \xs -> let arrows = map include xs
             in metadata (composeAll arrows) === Sum (sum xs)

  , testProperty "composeAll [] is identity (Sum 0)" $
      metadata (composeAll [] :: EnrichedArrow Sum DecisionState DecisionState) === Sum 0

  , testProperty "mixed include/skip: only includes contribute to metadata" $
      \(xs :: [Int]) -> let arrows = concatMap (\x -> [include x, skip x]) xs
                        in metadata (composeAll arrows) === Sum (sum xs)
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 3: Brute-force solver correctness
-- ═══════════════════════════════════════════════════════════

bruteForceTests :: TestTree
bruteForceTests = testGroup "BruteForce solver"
  [ testProperty "path count is 2^n" $
      forAll smallList $ \xs ->
        length (allPaths xs) === 2 ^ length xs

  , testProperty "all solutions actually sum to target" $
      forAll genSubsetSumInstance $ \(xs, target) ->
        let solutions = solveBruteForce xs target
        in all (\(elems, _) -> sum elems == target) solutions

  , testProperty "metadata matches actual sum of included elements" $
      forAll smallList $ \xs ->
        let paths = allPaths xs
        in all (\(decs, arrow) -> getSum (metadata arrow) == sum (extractIncluded decs)) paths

  , testProperty "reachedTarget agrees with metadata inspection" $
      forAll genSubsetSumInstance $ \(xs, target) ->
        let paths = allPaths xs
        in all (\(_, arrow) -> reachedTarget target arrow == (getSum (metadata arrow) == target)) paths

  -- Concrete regression tests
  , testProperty "[3,7,5,2] target 10 has exactly 2 solutions" $
      let solutions = solveBruteForce [3,7,5,2] 10
          subsets = sort (map (sort . fst) solutions)
      in subsets === [[2,3,5], [3,7]]

  , testProperty "empty list, target 0 has one solution (empty subset)" $
      let solutions = solveBruteForce [] 0
      in length solutions === 1

  , testProperty "empty list, target > 0 has no solutions" $
      let solutions = solveBruteForce [] 5
      in length solutions === 0

  , testProperty "[1,2,3] target 7 has no solutions (max sum is 6)" $
      let solutions = solveBruteForce [1,2,3] 7
      in length solutions === 0
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 4: DP vs BruteForce comparison
-- (analogous to prop_eq in mlabs-test: transformation preserves semantics)
-- ═══════════════════════════════════════════════════════════

dpComparisonTests :: TestTree
dpComparisonTests = testGroup "DP vs BruteForce (quotient preserves answer)"
  [ testProperty "BF and DP find the same solutions" $
      forAll genSubsetSumInstance $ \(xs, target) ->
        let cr = compareApproaches xs target
        in agree cr === True

  , testProperty "DP equiv classes <= BF path count" $
      forAll smallList $ \xs ->
        let cr = compareApproaches xs 0
        in dpClassCount cr <= bfPathCount cr

  , testProperty "DP solutions all sum to target" $
      forAll genSubsetSumInstance $ \(xs, target) ->
        all (\sol -> sum sol == target) (solveDPAll xs target)

  , testProperty "[3,7,5,2] target 10: DP agrees with BF" $
      let cr = compareApproaches [3,7,5,2] 10
      in (agree cr, sort (map sort (dpSolutions cr))) === (True, [[2,3,5], [3,7]])
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 5: Quotient & Functor properties
-- ═══════════════════════════════════════════════════════════

quotientFunctorTests :: TestTree
quotientFunctorTests = testGroup "Quotient & Functor"
  [ testProperty "quotient size <= number of morphisms" $
      forAll smallList $ \xs ->
        let arrows = map snd (allPaths xs)
            qhom = quotientByMetadata arrows
        in quotientSize qhom <= length arrows

  , testProperty "identity functor preserves metadata" $
      \n -> let f = include n
                mapped = mapArrow identityFunctor f
            in metadata mapped === metadata f

  -- mod k is a homomorphism (Z,+) -> (Z/kZ,+), meaning:
  -- (a + b) mod k == ((a mod k) + (b mod k)) mod k
  -- Note: Sum's <> is plain +, so we must apply mod k to the result too.
  , testProperty "modular functor: (a+b) mod k == ((a mod k) + (b mod k)) mod k" $
      forAll (choose (2, 50)) $ \k ->
        \(Positive a, Positive b) ->
          let mf = modularFunctor k
          in mapMeta mf (Sum a <> Sum b) === Sum ((getSum (mapMeta mf (Sum a)) + getSum (mapMeta mf (Sum b))) `mod` k)

  -- The functor correctly maps the metadata of a composed arrow:
  -- metadata(map(f ⊕ g)) == (a + b) mod k
  , testProperty "modular functor maps composed arrow correctly" $
      forAll (choose (2, 50)) $ \k ->
        \(Positive a, Positive b) ->
          let mf = modularFunctor k
              composed = include a ⊕ include b
          in metadata (mapArrow mf composed) === Sum ((a + b) `mod` k)

  , testProperty "quotient after functor has <= k classes (mod k)" $
      forAll (choose (2, 20)) $ \k ->
        forAll smallList $ \xs ->
          let arrows = map snd (allPaths xs)
              mapped = applyFunctor (modularFunctor k) arrows
              qhom = quotientByMetadata mapped
          in quotientSize qhom <= k

  , testProperty "lookupTarget finds reachable sums" $
      forAll genSubsetSumInstance $ \(xs, target) ->
        let arrows = map snd (allPaths xs)
            qhom = quotientByMetadata arrows
            hasSolution = not (null (solveBruteForce xs target))
            found = case lookupTarget (Sum target) qhom of Just _ -> True; Nothing -> False
        in found === hasSolution
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 6: Boolean Reduction (analogous to mlabs-test prop_eq)
-- ═══════════════════════════════════════════════════════════

booleanReductionTests :: TestTree
booleanReductionTests = testGroup "Boolean Reduction (SubsetSum <-> SAT)"
  [ -- The core property: like mlabs-test's prop_eq verifying
    -- evaluate i pl == evaluateNOR i (toNOR pl),
    -- we verify that BF solutions satisfy the SAT formula.
    testProperty "BF solutions satisfy SAT formula" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        let formula = subsetSumToSAT xs target
            solutionPaths = [ path | (path, arrow) <- allPaths xs, reachedTarget target arrow ]
        in all (\path -> evaluate (decisionPathToAssignment path) formula) solutionPaths

  , testProperty "non-solutions do NOT satisfy SAT formula" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        let formula = subsetSumToSAT xs target
            nonSolutionPaths = [ path | (path, arrow) <- allPaths xs, not (reachedTarget target arrow) ]
        in all (\path -> not (evaluate (decisionPathToAssignment path) formula)) nonSolutionPaths

  , testProperty "SAT formula is satisfiable iff BF has solutions" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        let formula = subsetSumToSAT xs target
            hasBFSolution = not (null (solveBruteForce xs target))
            -- Check all assignments
            n = length xs
            allAssignments = [Map.fromList (zip [0..] mask) | mask <- allBoolMasks n]
            hasSATSolution = any (\a -> evaluate a formula) allAssignments
        in hasBFSolution === hasSATSolution

  , testProperty "[3,7,5,2] target 10: SAT formula is satisfiable" $
      let formula = subsetSumToSAT [3,7,5,2] 10
          -- {3,7}: x0=T, x1=T, x2=F, x3=F
          assignment = Map.fromList [(0, True), (1, True), (2, False), (3, False)]
      in evaluate assignment formula === True
  ]

allBoolMasks :: Int -> [[Bool]]
allBoolMasks 0 = [[]]
allBoolMasks n = [b : rest | b <- [True, False], rest <- allBoolMasks (n - 1)]

-- ═══════════════════════════════════════════════════════════
-- Generators
-- ═══════════════════════════════════════════════════════════

-- | Small lists to keep brute-force feasible
smallList :: Gen [Int]
smallList = do
  n <- choose (0, 10)
  vectorOf n (choose (1, 20))

-- | Small instance for SAT tests (formula size is exponential)
genSmallSubsetSumInstance :: Gen ([Int], Int)
genSmallSubsetSumInstance = do
  n <- choose (0, 6)
  xs <- vectorOf n (choose (1, 10))
  if null xs
    then return (xs, 0)
    else do
      mask <- vectorOf (length xs) (arbitrary :: Gen Bool)
      let target = sum [x | (x, True) <- zip xs mask]
      return (xs, target)

-- | Generate a Subset Sum instance with a reachable target
genSubsetSumInstance :: Gen ([Int], Int)
genSubsetSumInstance = do
  xs <- smallList
  if null xs
    then return (xs, 0)
    else do
      -- Pick a random subset to make the target reachable
      mask <- vectorOf (length xs) (arbitrary :: Gen Bool)
      let target = sum [x | (x, True) <- zip xs mask]
      return (xs, target)
