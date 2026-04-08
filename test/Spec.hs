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
import PeqNP.Functor (EnrichedFunctor(..), applyFunctor, modularFunctor, identityFunctor, withModulus)
import PeqNP.BooleanReduction (subsetSumToSAT, evaluate, decisionPathToAssignment)
import PeqNP.FiniteMonoid (ZMod(..), BoolOr(..))
import qualified PeqNP.FiniteMonoid as FM
import PeqNP.Search (searchMonoid, MonoidReport(..))
import PeqNP.Impossibility (minDistinguishingModulus, MinSizeResult(..))
import PeqNP.DPSolver (dpReachable)
import PeqNP.ReachMonad (buildReachTree, totalDistinctStates, distinctStatesPerLevel, reachSetOf)
import PeqNP.MyhillNerode (mnClassify, MNResult(..), mnClassesPerLevel)
import PeqNP.VariableOrdering (naturalOrder, sortedAsc, greedyMinStates, OrderingResult(..))
import PeqNP.Polynomial (Poly, polyOne, includeFactor, coeffAt, hasCoeff, expand, ProductForm(..), polyMul)
import PeqNP.PolyQuotient (buildProductMod, polyModHasCoeff, minPreservingQ)
import PeqNP.NTT (evalProductAt)
import PeqNP.Relaxation (solveRelaxed, RelaxedSolution(..))
import PeqNP.Landscape (buildLandscape, ProbLandscape(..))
import PeqNP.LazyTree (searchWithStats, PruneStats(..))
import PeqNP.Streaming (streamingSolve, StreamStats(..))
import PeqNP.Diagonal (diagonalExperiment, DiagonalResult(..), greedyLargest, greedySmallest, thresholdHalf)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

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
  , finiteMonoidTests
  , correctedFunctorTests
  , preservationTests
  , reachMonadTests
  , myhillNerodeTests
  , variableOrderingTests
  , polynomialTests
  , probabilisticTests
  , lazyTreeTests
  , streamingTests
  , diagonalTests
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
-- Group 7: Finite monoid laws
-- ═══════════════════════════════════════════════════════════

finiteMonoidTests :: TestTree
finiteMonoidTests = testGroup "Finite monoid laws"
  [ testProperty "ZMod 7: associativity" $
      \(a, b, c) ->
        let za = ZMod a :: ZMod 7
            zb = ZMod b :: ZMod 7
            zc = ZMod c :: ZMod 7
        in (za <> zb) <> zc === za <> (zb <> zc)

  , testProperty "ZMod 7: identity" $
      \a -> let za = ZMod (a `mod` 7) :: ZMod 7
            in (mempty <> za === za) .&&. (za <> mempty === za)

  , testProperty "ZMod k: closure (result < k)" $
      forAll (choose (2, 50)) $ \k ->
        \(Positive a, Positive b) ->
          withModulus k $ \ef ->
            let result = mapMeta ef (Sum a) <> mapMeta ef (Sum b)
            in getZMod result >= 0 .&&. getZMod result < k

  , testProperty "BoolOr: identity is False" $
      (mempty :: BoolOr) === BoolOr False

  , testProperty "BoolOr: True absorbs" $
      \b -> BoolOr True <> BoolOr b === BoolOr True

  , testProperty "BoolOr: elements has 2 elements" $
      length (FM.elements :: [BoolOr]) === 2
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 8: Corrected functor (ZMod k IS a true homomorphism)
-- ═══════════════════════════════════════════════════════════

correctedFunctorTests :: TestTree
correctedFunctorTests = testGroup "Corrected enriched functor (ZMod k)"
  [ -- THE KEY FIX: with proper ZMod k, the homomorphism property holds exactly
    testProperty "ZMod k: h(a+b) == h(a) <> h(b) (TRUE homomorphism)" $
      forAll (choose (2, 50)) $ \k ->
        \(Positive a, Positive b) ->
          withModulus k $ \ef ->
            mapMeta ef (Sum a <> Sum b) === (mapMeta ef (Sum a) <> mapMeta ef (Sum b))

  , testProperty "ZMod k: functor preserves composition metadata" $
      forAll (choose (2, 50)) $ \k ->
        \(Positive a, Positive b) ->
          withModulus k $ \ef ->
            let composed = include a ⊕ include b
                mappedComposed = mapArrow ef composed
                composedMapped = mapArrow ef (include a) ⊕ mapArrow ef (include b)
            in metadata mappedComposed === metadata composedMapped

  , testProperty "ZMod k: maps identity to identity" $
      forAll (choose (2, 50)) $ \k ->
        withModulus k $ \ef ->
          mapMeta ef (mempty :: Sum) === mempty
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 9: Answer preservation
-- ═══════════════════════════════════════════════════════════

preservationTests :: TestTree
preservationTests = testGroup "Answer preservation"
  [ -- YES instances: every homomorphism preserves the answer
    testProperty "YES instances: all homomorphisms preserve" $
      forAll genSubsetSumInstance $ \(xs, target) ->
        not (null (solveBruteForce xs target)) ==>
          let report = searchMonoid @(ZMod 7) "Z/7Z" xs target
          in mrAnyPreserve report === True

  , testProperty "ZMod k with k > max_sum always preserves" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        let maxSum = sum (map abs xs) + 1
        in maxSum > 1 ==>
             let result = minDistinguishingModulus xs target (maxSum + 10)
             in case msrMinModulus result of
                  Just k  -> k <= maxSum + 1
                  Nothing -> msrTargetReachable result

  , testProperty "[3,7,5,2] target 11 (NO): min modulus is 5" $
      msrMinModulus (minDistinguishingModulus [3,7,5,2] 11 100) === Just 5

  , testProperty "[3,7,5,2] target 10 (YES): any modulus works" $
      msrMinModulus (minDistinguishingModulus [3,7,5,2] 10 100) === Just 1
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 10: Reachability monad
-- ═══════════════════════════════════════════════════════════

reachMonadTests :: TestTree
reachMonadTests = testGroup "Reachability monad"
  [ testProperty "root reachSet matches dpReachable" $
      forAll smallList $ \xs ->
        let tree = buildReachTree xs
        in reachSetOf tree === dpReachable xs

  , testProperty "distinct states per level is monotonically bounded by 2^level" $
      forAll smallList $ \xs ->
        let levels = distinctStatesPerLevel (buildReachTree xs)
        in all (\(i, count) -> count <= 2^i) (zip [(0::Int)..] levels)

  , testProperty "leaf level has exactly 2^n states or fewer" $
      forAll smallList $ \xs ->
        let levels = distinctStatesPerLevel (buildReachTree xs)
        in last levels <= 2 ^ length xs
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 11: Myhill-Nerode
-- ═══════════════════════════════════════════════════════════

myhillNerodeTests :: TestTree
myhillNerodeTests = testGroup "Myhill-Nerode equivalence"
  [ testProperty "MN classes always <= 2 per level" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        not (null xs) ==>
          all (<= 2) (mnClassesPerLevel xs target)

  , testProperty "MN classes <= distinct sums at each level" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        not (null xs) ==>
          let mn = mnClassify xs target
          in and (zipWith (<=) (mnClassesPerLvl mn) (mnSumsPerLvl mn))

  , testProperty "[3,7,5,2] target 10: MN has at most 2 classes" $
      all (<= 2) (mnClassesPerLevel [3,7,5,2] 10)
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 12: Variable ordering
-- ═══════════════════════════════════════════════════════════

variableOrderingTests :: TestTree
variableOrderingTests = testGroup "Variable ordering"
  [ testProperty "all orderings reach same final state count" $
      forAll smallList $ \xs ->
        not (null xs) ==>
          let natFinal = last (orStatesPerLevel (naturalOrder xs))
              ascFinal = last (orStatesPerLevel (sortedAsc xs))
          in natFinal === ascFinal

  , testProperty "greedy never worse than natural order" $
      forAll smallList $ \xs ->
        not (null xs) ==>
          orMaxStates (greedyMinStates xs) <= orMaxStates (naturalOrder xs)

  , testProperty "final level = number of distinct reachable sums" $
      forAll smallList $ \xs ->
        let finalStates = last (orStatesPerLevel (naturalOrder xs))
        in finalStates === Set.size (dpReachable xs)
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 13: Polynomial enrichment
-- ═══════════════════════════════════════════════════════════

polynomialTests :: TestTree
polynomialTests = testGroup "Polynomial enrichment"
  [ testProperty "expand matches brute-force reachable sums" $
      forAll smallList $ \xs ->
        let poly = expand (PF xs)
            reachable = dpReachable xs
        in Set.fromList [e | e <- [0..sum xs], hasCoeff e poly]
           === reachable

  , testProperty "polyMul is associative" $
      \(Positive a, Positive b, Positive c) ->
        let pa = includeFactor a
            pb = includeFactor b
            pc = includeFactor c
        in (pa <> pb) <> pc === pa <> (pb <> pc)

  , testProperty "polyOne is identity" $
      \(Positive a) ->
        let pa = includeFactor a
        in (polyOne <> pa === pa) .&&. (pa <> polyOne === pa)

  , testProperty "coeffAt T in expand matches hasCoeff" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        let poly = expand (PF xs)
        in (coeffAt target poly > 0) === hasCoeff target poly

  , testProperty "quotient with q > max_sum preserves answer" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        not (null xs) ==>
          let maxS = sum xs + 1
              pm = buildProductMod maxS xs
              poly = expand (PF xs)
          in polyModHasCoeff target pm === hasCoeff target poly

  , testProperty "evalProductAt: g(1) mod p = 2^n mod p" $
      forAll smallList $ \xs ->
        not (null xs) ==>
          let p = 97  -- prime
              g1 = evalProductAt p 1 xs
          in g1 === ((2 ^ length xs) `mod` p)

  , testProperty "[3,7,5,2] target 11: min q = 5" $
      minPreservingQ [3,7,5,2] 11 100 === Just 5
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 14: Probabilistic approach
-- ═══════════════════════════════════════════════════════════

probabilisticTests :: TestTree
probabilisticTests = testGroup "Probabilistic approach"
  [ testProperty "LP relaxation: residual is ~0" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        not (null xs) && target > 0 && target <= sum xs ==>
          rsResidual (solveRelaxed xs target) < 0.001

  , testProperty "LP relaxation: all fractions in [0,1]" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        not (null xs) && target >= 0 && target <= sum xs ==>
          let fracs = rsFractions (solveRelaxed xs target)
          in all (\f -> f >= 0 && f <= 1.0001) fracs

  , testProperty "LP relaxation: confidence in [0,1]" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        not (null xs) && target >= 0 && target <= sum xs ==>
          let c = rsConfidence (solveRelaxed xs target)
          in c >= 0 && c <= 1.0001

  , testProperty "Landscape: P(hit) = 0 for NO instances" $
      let noInsts = [([3,7,5,2], 11), ([1,2,3], 7), ([1,2], 4)]
      in all (\(xs, t) -> plTargetProb (buildLandscape 100 xs t) == 0) noInsts

  , testProperty "Landscape: P(hit) > 0 for easy YES instances" $
      -- [5,5] target=5: LP gives [1,0] → rounding always hits
      plTargetProb (buildLandscape 100 [5, 5] 5) > 0
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 15: Lazy tree pruning
-- ═══════════════════════════════════════════════════════════

lazyTreeTests :: TestTree
lazyTreeTests = testGroup "Lazy tree pruning"
  [ testProperty "finds correct solutions (YES instances)" $
      forAll genSubsetSumInstance $ \(xs, target) ->
        not (null xs) ==>
          let ps = searchWithStats xs target
              hasSolution = not (null (solveBruteForce xs target))
          in (psSolution ps /= Nothing) === hasSolution

  , testProperty "[3,7,5,2] target=10 finds solution" $
      psSolution (searchWithStats [3,7,5,2] 10) /= Nothing
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 16: Streaming solver
-- ═══════════════════════════════════════════════════════════

streamingTests :: TestTree
streamingTests = testGroup "Streaming solver"
  [ testProperty "agrees with brute force" $
      forAll genSubsetSumInstance $ \(xs, target) ->
        not (null xs) ==>
          let hasBF = not (null (solveBruteForce xs target))
          in stFound (streamingSolve xs target) === hasBF

  , testProperty "peak live sums <= DP distinct sums" $
      forAll genSmallSubsetSumInstance $ \(xs, target) ->
        not (null xs) ==>
          stMaxLive (streamingSolve xs target) <= Set.size (dpReachable xs)

  , testProperty "[3,7,5,2] target=10 found" $
      stFound (streamingSolve [3,7,5,2] 10) === True
  ]

-- ═══════════════════════════════════════════════════════════
-- Group 17: Diagonal argument
-- ═══════════════════════════════════════════════════════════

diagonalTests :: TestTree
diagonalTests = testGroup "Diagonal argument"
  [ testProperty "greedy-largest is defeated" $
      case diagonalExperiment [greedyLargest] of
        [r] -> drDefeatedAtN r /= Nothing
        _   -> False

  , testProperty "all simple strategies defeated at n <= 12" $
      let results = diagonalExperiment [greedyLargest, greedySmallest, thresholdHalf]
      in all (\r -> drDefeatedAtN r /= Nothing) results

  , testProperty "counterexamples are valid" $
      let results = diagonalExperiment [greedyLargest, greedySmallest]
      in all (\r -> case drCounterexample r of
                Nothing -> True  -- not defeated = ok
                Just (es, t, ans) -> (Set.member t (dpReachable es)) == ans
             ) results
  ]

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
