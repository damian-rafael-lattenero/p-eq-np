module Main where

import PeqNP.EnrichedArrow (EnrichedArrow(..))
import PeqNP.Composition ((⊕))
import PeqNP.SubsetSum (Sum(..), DecisionState(..), include, skip, reachedTarget)
import PeqNP.BruteForce (allPaths, solveBruteForce, Decision(..), Path)
import PeqNP.Comparison (compareApproaches, showComparison)
import PeqNP.Quotient (quotientByMetadata, quotientSize, lookupTarget)
import PeqNP.Functor (EnrichedFunctor(..), applyFunctor, modularFunctor, forgetfulFunctor)
import PeqNP.BooleanReduction (subsetSumToSAT, evaluate, decisionPathToAssignment, showReduction)
import PeqNP.FiniteMonoid (ZMod(..))
import PeqNP.Search (searchMonoid, MonoidReport(..), SearchResult(..))
import PeqNP.Impossibility (minDistinguishingModulus, MinSizeResult(..), scalingAnalysis, ScalingDataPoint(..))
import PeqNP.Report (showMonoidReport, showScalingTable)
import PeqNP.ReachMonad (buildReachTree, showReachTree, distinctStatesPerLevel, totalDistinctStates)
import PeqNP.MyhillNerode (mnClassify, MNResult(..))
import PeqNP.VariableOrdering (naturalOrder, sortedAsc, sortedDesc, greedyMinStates, showOrderingResult)
import PeqNP.CategoryExperiments (showComparisonTable)
import PeqNP.Polynomial (expand, ProductForm(..), showPoly, nonzeroTerms, hasCoeff)
import PeqNP.PolyQuotient (buildProductMod, polyModHasCoeff, polyModCoeffAt, polyScaling, PolyScalingPoint(..))
import PeqNP.NTT (evalProductAt, nttCoeffAt)
import PeqNP.Relaxation (solveRelaxed, showRelaxed, RelaxedSolution(..))
import PeqNP.Rounding (probabilisticSolve, showStats)
import PeqNP.Landscape (buildLandscape, showLandscape, showHistogram, ProbLandscape(..))

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " P=NP? Enriched Category Theory approach via Subset Sum"
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  let elements = [3, 7, 5, 2]
      target   = 10

  putStrLn $ "Problem: elements = " ++ show elements ++ ", target = " ++ show target
  putStrLn ""

  -- Demonstrate enriched composition by hand
  sectionHeader "1. Manual enriched composition"
  let manualPath = include 3 ⊕ skip 7 ⊕ include 5 ⊕ include 2
  putStrLn "  include 3 ⊕ skip 7 ⊕ include 5 ⊕ include 2"
  putStrLn $ "  metadata    = " ++ show (metadata manualPath)
  putStrLn $ "  reachedTarget 10 = " ++ show (reachedTarget target manualPath)
  putStrLn ""
  putStrLn "  KEY INSIGHT: metadata was computed during COMPOSITION,"
  putStrLn "  not during execution. The arrow hasn't been applied yet."
  putStrLn ""

  -- Now actually run it to confirm
  let initialState = DS { remaining = elements, included = [] }
      result = runArrow manualPath initialState
  putStrLn $ "  Running the arrow: included = " ++ show (included result)
  putStrLn ""

  -- Enumerate all paths
  sectionHeader "2. All 2^n decision paths"
  let paths = allPaths elements
  putStrLn $ "  Total paths: " ++ show (length paths) ++ " (2^" ++ show (length elements) ++ ")"
  putStrLn ""
  mapM_ showPath paths
  putStrLn ""

  -- Solve
  sectionHeader "3. Solutions (filtered by metadata only)"
  let solutions = solveBruteForce elements target
  putStrLn $ "  Found " ++ show (length solutions) ++ " solution(s) summing to " ++ show target ++ ":"
  mapM_ showSolution solutions
  putStrLn ""

  -- Compare BF vs DP
  sectionHeader "4. BruteForce vs DP (categorical quotienting)"
  putStrLn "  DP quotients the hom-object by metadata equivalence:"
  putStrLn "  paths with the same partial sum collapse into one class."
  putStrLn ""
  let comparison = compareApproaches elements target
  putStr $ showComparison comparison
  putStrLn ""

  -- Quotient hom-object
  sectionHeader "5. Explicit categorical quotienting"
  let allArrows = map snd paths
      qhom = quotientByMetadata allArrows
  putStrLn $ "  Full hom-object:      " ++ show (length allArrows) ++ " morphisms"
  putStrLn $ "  Quotiented hom-object: " ++ show (quotientSize qhom) ++ " equivalence classes"
  putStrLn $ "  Target " ++ show target ++ " reachable?  "
          ++ show (case lookupTarget (Sum target) qhom of Just _ -> True; Nothing -> False)
  putStrLn ""

  -- Functors
  sectionHeader "6. Enriched functors (monoid homomorphisms)"
  putStrLn "  Applying functors to all 16 paths and quotienting the image:"
  putStrLn ""

  let showFunctorResult :: EnrichedFunctor Sum Sum -> IO ()
      showFunctorResult ef = do
        let mapped = applyFunctor ef allArrows
            qMapped = quotientByMetadata mapped
            targetMapped = mapMeta ef (Sum target)
            found = case lookupTarget targetMapped qMapped of Just _ -> True; Nothing -> False
        putStrLn $ "  F = " ++ padRight 12 (functorName ef)
                ++ " | classes: " ++ padRight 4 (show (quotientSize qMapped))
                ++ " | target " ++ padRight 12 (show targetMapped)
                ++ " reachable: " ++ show found

  showFunctorResult (modularFunctor 3)
  showFunctorResult (modularFunctor 5)
  showFunctorResult (modularFunctor 7)
  showFunctorResult (modularFunctor 11)
  showFunctorResult (modularFunctor 17)
  putStrLn ""
  putStrLn "  Forgetful functor (all info lost):"
  let forgottenArrows = applyFunctor forgetfulFunctor allArrows
      qForgotten = quotientByMetadata forgottenArrows
  putStrLn $ "  F = forgetful   | classes: " ++ show (quotientSize qForgotten)
          ++ " (everything collapses to ())"
  putStrLn ""

  putStrLn "  THE P=NP QUESTION: does there exist a functor F to a"
  putStrLn "  finite monoid of polynomial size that PRESERVES the answer?"
  putStrLn "  mod k works when target is distinguishable mod k,"
  putStrLn "  but fails when distinct sums collide. The search continues..."
  putStrLn ""

  -- Boolean reduction: Subset Sum ↔ SAT
  sectionHeader "7. Subset Sum as Boolean SAT (inspired by mlabs-test)"
  putStrLn "  Just as mlabs-test's toNOR : PLSentence -> NORSentence"
  putStrLn "  is a functor preserving evaluation, subsetSumToSAT"
  putStrLn "  transforms the decision-category problem into SAT."
  putStrLn ""
  putStr $ showReduction elements target
  putStrLn ""

  -- Verify: each BF solution path, converted to assignment, satisfies the formula
  let formula = subsetSumToSAT elements target
  putStrLn "  Verifying: BF solutions satisfy the SAT formula?"
  let bfPaths = [ path | (path, arrow) <- allPaths elements, reachedTarget target arrow ]
  mapM_ (\path -> do
    let assignment = decisionPathToAssignment path
        sat = evaluate assignment formula
    putStrLn $ "    " ++ showDecisions path ++ " -> SAT = " ++ show sat
    ) bfPaths
  putStrLn ""

  putStrLn "  THE UNIFIED VIEW:"
  putStrLn "  Subset Sum, SAT, and the enriched category are three views"
  putStrLn "  of the same problem. The functors between them preserve"
  putStrLn "  the answer. P=NP asks: does any of these views admit"
  putStrLn "  a polynomial-time algorithm?"
  putStrLn ""

  -- Systematic search on finite monoids
  sectionHeader "8. Systematic functor search (ZMod k)"
  putStrLn "  For a NO instance: [3,7,5,2] target 11 (no subset sums to 11)"
  putStrLn ""

  let noElements = [3, 7, 5, 2]
      noTarget   = 11
  let report3 = searchMonoid @(ZMod 3) "Z/3Z" noElements noTarget
  putStrLn $ showMonoidReport report3
  let report7 = searchMonoid @(ZMod 7) "Z/7Z" noElements noTarget
  putStrLn $ showMonoidReport report7
  let report11 = searchMonoid @(ZMod 11) "Z/11Z" noElements noTarget
  putStrLn $ showMonoidReport report11

  putStrLn "  Minimum distinguishing modulus search (k = 2..100):"
  let minResult = minDistinguishingModulus noElements noTarget 100
  putStrLn $ "    Distinct reachable sums: " ++ show (msrDistinctSums minResult)
  putStrLn $ "    Min k that works:        " ++ show (msrMinModulus minResult)
  putStrLn ""

  -- Scaling experiment
  sectionHeader "9. Scaling experiment: how does min k grow with n?"
  putStrLn "  For hard NO instances with increasing n:"
  putStrLn ""

  -- Hand-crafted NO instances of increasing size
  let hardInstances =
        [ ([1, 2], 4)                                  -- n=2
        , ([1, 2, 3], 7)                               -- n=3
        , ([1, 2, 3, 5], 12)                           -- n=4
        , ([1, 2, 3, 5, 8], 20)                        -- n=5
        , ([1, 2, 3, 5, 8, 13], 33)                    -- n=6
        , ([1, 2, 3, 5, 8, 13, 21], 54)                -- n=7
        , ([1, 2, 3, 5, 8, 13, 21, 34], 88)            -- n=8
        , ([2, 5, 11, 23, 47, 97, 193, 389, 769], 1537) -- n=9, powers-ish
        ]
  let scaling = scalingAnalysis hardInstances 500
  putStr $ showScalingTable scaling
  putStrLn ""
  putStrLn "  If min k grows polynomially in n -> evidence for P = NP"
  putStrLn "  If min k grows exponentially in n -> evidence for P /= NP"
  putStrLn ""

  -- Phase F: Beyond monoid homomorphisms
  sectionHeader "10. Reachability monad (forward analysis)"
  let smallElems = [3, 7, 5, 2]
  let rTree = buildReachTree smallElems
  putStr $ showReachTree rTree
  putStrLn ""

  sectionHeader "11. Myhill-Nerode equivalence classes"
  putStrLn "  How many MN classes vs distinct sums per level?"
  putStrLn "  (MN classes = states distinguishable by future behavior)"
  putStrLn ""
  let mn = mnClassify smallElems 10
  putStrLn $ "  Instance: " ++ show smallElems ++ " target=10"
  putStrLn $ "  MN classes/level:  " ++ show (mnClassesPerLvl mn)
  putStrLn $ "  Distinct sums/level: " ++ show (mnSumsPerLvl mn)
  putStrLn ""
  putStrLn "  KEY: MN classes are always <= 2 (reach/not-reach target)."
  putStrLn "  But determining which class = solving the problem!"
  putStrLn ""

  sectionHeader "12. Variable ordering (BDD-like)"
  putStrLn "  Same instance, different processing orders:"
  putStrLn ""
  let fibElems = [1, 2, 3, 5, 8, 13]
  putStrLn $ "  Elements: " ++ show fibElems
  putStrLn $ showOrderingResult (naturalOrder fibElems)
  putStrLn $ showOrderingResult (sortedAsc fibElems)
  putStrLn $ showOrderingResult (sortedDesc fibElems)
  putStrLn $ showOrderingResult (greedyMinStates fibElems)
  putStrLn ""

  sectionHeader "13. All categorical constructions compared"
  putStr $ showComparisonTable smallElems 10
  putStrLn ""
  putStr $ showComparisonTable [1,2,3,5,8] 20
  putStrLn ""

  -- Phase G: Polynomial enrichment
  sectionHeader "14. Generating function: O(n) encoding of 2^n sums"
  let gfElems = [3, 7, 5, 2]
  putStrLn $ "  g(x) = Π(1 + x^wᵢ) for " ++ show gfElems
  let fullPoly = expand (PF gfElems)
  putStrLn $ "  Expanded: " ++ showPoly fullPoly
  putStrLn $ "  Nonzero terms: " ++ show (nonzeroTerms fullPoly) ++ " (out of 2^4 = 16 possible)"
  putStrLn $ "  [x^10] = " ++ show (hasCoeff 10 fullPoly) ++ " (target 10 reachable!)"
  putStrLn $ "  [x^11] = " ++ show (hasCoeff 11 fullPoly) ++ " (target 11 not reachable)"
  putStrLn ""

  sectionHeader "15. Polynomial quotient Z[x]/(x^q - 1)"
  putStrLn "  Quotienting wraps x^k → x^(k mod q). Smaller q = more compression."
  putStrLn "  For NO instance: [3,7,5,2] target=11"
  putStrLn ""
  let noE = [3,7,5,2]
      noT = 11
  mapM_ (\q -> do
    let pm = buildProductMod q noE
        fp = polyModHasCoeff noT pm
        c  = polyModCoeffAt noT pm
    putStrLn $ "  q=" ++ padRight 4 (show q)
            ++ " [x^" ++ show noT ++ " mod " ++ show q ++ "]=" ++ padRight 4 (show c)
            ++ " false positive: " ++ show fp
    ) [3, 5, 7, 11, 13, 17]
  putStrLn ""

  sectionHeader "16. Poly quotient vs ZMod k: scaling comparison"
  let scalingInstances =
        [ ([1, 2], 4)
        , ([1, 2, 3], 7)
        , ([1, 2, 3, 5], 12)
        , ([1, 2, 3, 5, 8], 20)
        , ([1, 2, 3, 5, 8, 13], 33)
        , ([1, 2, 3, 5, 8, 13, 21], 54)
        ]
  let pScaling = polyScaling scalingInstances 200
  putStrLn "  n    target  min_q (poly)  min_k (ZMod)"
  putStrLn $ "  " ++ replicate 45 '-'
  mapM_ (\p -> putStrLn $ "  " ++ padRight 5 (show (pspN p))
                        ++ padRight 8 (show (pspTarget p))
                        ++ padRight 14 (maybe "N/A" show (pspMinQ p))
                        ++ maybe "N/A" show (pspMinK p)
    ) pScaling
  putStrLn ""

  -- NTT demo
  sectionHeader "17. NTT: O(n) evaluation at roots of unity"
  putStrLn "  Evaluating g(x) = Π(1+x^wᵢ) at point α mod p takes O(n)!"
  putStrLn $ "  g(2) mod 97 = " ++ show (evalProductAt 97 2 gfElems)
  putStrLn $ "  g(3) mod 97 = " ++ show (evalProductAt 97 3 gfElems)
  case nttCoeffAt 97 8 10 gfElems of
    Just c  -> putStrLn $ "  NTT: [x^10] g(x) mod 97 = " ++ show c ++ " (should be > 0)"
    Nothing -> putStrLn "  NTT: no 8th root of unity mod 97"
  case nttCoeffAt 97 8 11 gfElems of
    Just c  -> putStrLn $ "  NTT: [x^11] g(x) mod 97 = " ++ show c ++ " (should be 0 if q big enough)"
    Nothing -> putStrLn "  NTT: no 8th root of unity mod 97"
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " The generating function approach enriches over Z[x]"
  putStrLn " instead of Z. The quotient Z[x]/(x^q-1) compresses"
  putStrLn " using multiplicative structure, not just additive."
  putStrLn " If min_q < min_k for hard instances, polynomials WIN."
  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn ""

  -- Phase H: Probabilistic approach
  sectionHeader "18. LP relaxation: continuous [0,1] solution"
  let lpElems = [3, 7, 5, 2]
  putStr $ showRelaxed (solveRelaxed lpElems 10)
  putStrLn ""
  putStr $ showRelaxed (solveRelaxed [1,2,3,5,8,13] 15)
  putStrLn ""

  sectionHeader "19. Probabilistic solver (randomized rounding)"
  putStrLn "  [3,7,5,2] target=10:"
  let stats1 = probabilisticSolve 100 10 lpElems 10
  putStr $ showStats stats1
  putStrLn ""
  putStrLn "  [1,2,3,5,8,13] target=15:"
  let stats2 = probabilisticSolve 100 10 [1,2,3,5,8,13] 15
  putStr $ showStats stats2
  putStrLn ""

  sectionHeader "20. Probability landscape"
  let landscape = buildLandscape 1000 lpElems 10
  putStr $ showLandscape landscape
  putStrLn ""
  putStrLn "  Sum distribution (histogram):"
  putStr $ showHistogram landscape
  putStrLn ""

  sectionHeader "21. Scaling: P(hit) vs n"
  putStrLn "  How does target probability scale with instance size?"
  putStrLn ""
  let scalingInsts =
        [ ([3, 7], 10)
        , ([3, 7, 5], 10)
        , ([3, 7, 5, 2], 10)
        , ([1, 2, 3, 5, 8], 10)
        , ([1, 2, 3, 5, 8, 13], 10)
        , ([1, 2, 3, 5, 8, 13, 21], 10)
        ]
  putStrLn $ "  " ++ padRight 5 "n" ++ padRight 10 "P(hit)" ++ "E[trials]"
  putStrLn $ "  " ++ replicate 30 '-'
  mapM_ (\(es, t) -> do
    let l = buildLandscape 10000 es t
    putStrLn $ "  " ++ padRight 5 (show (length es))
            ++ padRight 10 (show (roundTo' 4 (plTargetProb l)))
            ++ (if plTargetProb l > 0
                then show (round (plExpectedTrials l) :: Int)
                else "Inf")
    ) scalingInsts
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " The probabilistic approach trades exactness for speed."
  putStrLn " P(hit) determines whether randomized rounding gives a"
  putStrLn " polynomial-time algorithm. If P(hit) >= 1/poly(n) for"
  putStrLn " all YES instances → Subset Sum in BPP → likely P = NP."
  putStrLn "═══════════════════════════════════════════════════════════"

roundTo' :: Int -> Double -> Double
roundTo' n x = fromIntegral (round (x * 10^n) :: Int) / 10^n

sectionHeader :: String -> IO ()
sectionHeader title = do
  putStrLn $ "── " ++ title ++ " ──"
  putStrLn ""

showPath :: (Path, EnrichedArrow Sum DecisionState DecisionState) -> IO ()
showPath (decisions, arrow) =
  putStrLn $ "  " ++ padRight 32 (showDecisions decisions)
          ++ " metadata = " ++ padRight 8 (show (metadata arrow))
          ++ (if reachedTarget 10 arrow then " <-- TARGET!" else "")

showDecisions :: [Decision] -> String
showDecisions = unwords . map showDec
  where
    showDec (Include x) = "+" ++ show x
    showDec (Skip x)    = "-" ++ show x

showSolution :: ([Int], EnrichedArrow Sum DecisionState DecisionState) -> IO ()
showSolution (elems, arrow) =
  putStrLn $ "  subset = " ++ show elems
          ++ ", metadata = " ++ show (metadata arrow)

padRight :: Int -> String -> String
padRight n s = s ++ replicate (max 0 (n - length s)) ' '
