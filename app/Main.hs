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
import PeqNP.NTT (evalProductAt, nttCoeffAt, modPow)
import PeqNP.LLL (lllSolve, showLLLResult, density)
import PeqNP.Topological (analyzeGaps, showGapAnalysis)
import PeqNP.DensityMap (densitySweep, showDensitySweep)
import PeqNP.Combined (combinedSolve, showCombinedResult, CombinedResult(..))
import PeqNP.Relaxation (solveRelaxed, showRelaxed, RelaxedSolution(..))
import PeqNP.Rounding (probabilisticSolve, showStats)
import PeqNP.Landscape (buildLandscape, showLandscape, showHistogram, ProbLandscape(..))
import PeqNP.LazyTree (searchWithStats, showPruneStats)
import PeqNP.Streaming (streamingSolve, showStreamStats)
import PeqNP.Diagonal (diagonalExperiment, showDiagonalResults, greedyLargest, greedySmallest, alwaysInclude, alwaysSkip, thresholdHalf, alternating)
import PeqNP.FingerTree (fingerTreeSolve, showFTStats, measureDifficulty, showDifficultyProfile)
import PeqNP.BitDecompose (analyzeCarry, showCarryProfile, bitLevelSolve, BitLevelStats(..), decomposeProblem, BitColumn(..), coupledBitSolve, showCoupledStats, untieRetieExperiment, showUntieRetie, interleavedSolve, showInterleavedStats, showBasisSearch, showGF2Results, solveInTransformedBasis, showGF2SolverResult, analyzeRank, showRankAnalysis, recursiveGF2Solve, showRecursiveResult, RecursiveResult(..), randomGF2Vote, showVoteResult)
import PeqNP.UnifiedExperiments (unifiedAnalysis, showUnifiedTable)

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
  putStrLn ""

  -- Phase I: Navigation, pruning, and diagonalization
  sectionHeader "22. Lazy tree with branch-and-bound pruning"
  putStrLn "  [3,7,5,2] target=10 (YES instance):"
  putStr $ showPruneStats (searchWithStats [3,7,5,2] 10)
  putStrLn ""
  putStrLn "  [1,2,3,5,8,13,21] target=54 (NO — sum+1):"
  putStr $ showPruneStats (searchWithStats [1,2,3,5,8,13,21] 54)
  putStrLn ""
  putStrLn "  [1,2,3,5,8,13,21] target=30 (YES):"
  putStr $ showPruneStats (searchWithStats [1,2,3,5,8,13,21] 30)
  putStrLn ""

  sectionHeader "23. Streaming solver (bubbling soda)"
  putStrLn "  [3,7,5,2] target=10:"
  putStr $ showStreamStats (streamingSolve [3,7,5,2] 10)
  putStrLn ""
  putStrLn "  [1,2,3,5,8,13] target=15:"
  putStr $ showStreamStats (streamingSolve [1,2,3,5,8,13] 15)
  putStrLn ""

  sectionHeader "24. Diagonal argument: defeating strategies"
  let strategies = [greedyLargest, greedySmallest, alwaysInclude, alwaysSkip, thresholdHalf, alternating]
  putStr $ showDiagonalResults (diagonalExperiment strategies)
  putStrLn ""
  putStrLn "  Every simple strategy is defeated at small n."
  putStrLn "  The question: does n_defeat grow with strategy complexity?"
  putStrLn ""

  sectionHeader "25. Finger tree with monoidal pruning"
  putStrLn "  Annotation [minSum, maxSum] enables O(1) prune per node."
  putStrLn ""
  putStrLn "  [3,7,5,2] target=10:"
  putStr $ showFTStats (fingerTreeSolve [3,7,5,2] 10)
  putStrLn ""
  putStrLn "  [1,2,3,5,8,13] target=15:"
  putStr $ showFTStats (fingerTreeSolve [1,2,3,5,8,13] 15)
  putStrLn ""
  putStrLn "  [1,2,3,5,8,13,21] target=54 (NO):"
  putStr $ showFTStats (fingerTreeSolve [1,2,3,5,8,13,21] 54)
  putStrLn ""

  sectionHeader "26. UNIFIED TABLE: all phases compared"
  let unifiedInstances =
        [ ([3, 7, 5, 2], 10)           -- n=4, YES
        , ([3, 7, 5, 2], 11)           -- n=4, NO
        , ([1, 2, 3, 5, 8], 10)        -- n=5, YES
        , ([1, 2, 3, 5, 8], 20)        -- n=5, NO
        , ([1, 2, 3, 5, 8, 13], 15)    -- n=6, YES
        , ([1, 2, 3, 5, 8, 13], 33)    -- n=6, NO
        ]
  putStr $ showUnifiedTable (unifiedAnalysis unifiedInstances)
  putStrLn ""

  sectionHeader "27. WHERE does NP-hardness appear? (TargetAware monoid)"
  putStrLn "  The perfect monoid tracks ALL reachable sums (Set Int)."
  putStrLn "  <> = sumset: {a+b | a in left, b in right}."
  putStrLn "  At which tree level does the set size EXPLODE past n²?"
  putStrLn ""

  putStrLn "  Sequential weights [1..6] (dense sums, polynomial growth):"
  putStr $ showDifficultyProfile (measureDifficulty [1,2,3,4,5,6])
  putStrLn ""

  putStrLn "  Fibonacci weights (exponential distinct sums):"
  putStr $ showDifficultyProfile (measureDifficulty [1,2,3,5,8,13])
  putStrLn ""

  putStrLn "  Super-increasing [1,2,4,8,16,32] (worst case: 2^n sums):"
  putStr $ showDifficultyProfile (measureDifficulty [1,2,4,8,16,32])
  putStrLn ""

  putStrLn "  KEY INSIGHT: for sequential weights, the annotation stays"
  putStrLn "  polynomial — that's WHY DP works (pseudo-poly). For super-"
  putStrLn "  increasing weights, it explodes at the middle levels."
  putStrLn "  NP-hardness lives in the MERGE, not the leaves."
  putStrLn ""

  sectionHeader "28. BIT DECOMPOSITION: treating Int as bits, not magnitude"
  putStrLn "  Key idea: at the type level, Int is Int. A weight of 5 and"
  putStrLn "  a weight of 5000000 have the same structure. By decomposing"
  putStrLn "  into bits, we process UNIFORMLY regardless of magnitude."
  putStrLn ""
  putStrLn "  The carry at each bit position is bounded by n/2 (not by"
  putStrLn "  the weight magnitude!). This means the bit-level solver"
  putStrLn "  is O(n² × log(max_weight)) — polynomial in INPUT SIZE."
  putStrLn ""

  putStrLn "  Sequential [1..6] target=10:"
  putStr $ showCarryProfile (analyzeCarry [1,2,3,4,5,6] 10)
  putStrLn ""

  putStrLn "  Fibonacci [1,2,3,5,8,13] target=15:"
  putStr $ showCarryProfile (analyzeCarry [1,2,3,5,8,13] 15)
  putStrLn ""

  putStrLn "  Super-increasing [1,2,4,8,16,32] target=21:"
  putStr $ showCarryProfile (analyzeCarry [1,2,4,8,16,32] 21)
  putStrLn ""

  putStrLn "  EXPONENTIAL weights [100,200,400,800,1600] target=1000:"
  putStr $ showCarryProfile (analyzeCarry [100,200,400,800,1600] 1000)
  putStrLn ""

  putStrLn "  BIG weights [1000000,2000000,3000000] target=4000000:"
  putStr $ showCarryProfile (analyzeCarry [1000000,2000000,3000000] 4000000)
  putStrLn ""

  sectionHeader "29. COUPLED bit solver: the REAL state count"
  putStrLn "  The uncoupled solver was wrong (false positives!)."
  putStrLn "  The coupled solver tracks (carry, which_weights_included)."
  putStrLn "  HOW BIG does the state space get when coupling is enforced?"
  putStrLn ""

  putStrLn "  [3,7,5,2] target=11 (NO — uncoupled said YES!):"
  putStr $ showCoupledStats (coupledBitSolve [3,7,5,2] 11)
  putStrLn ""

  putStrLn "  [3,7,5,2] target=10 (YES):"
  putStr $ showCoupledStats (coupledBitSolve [3,7,5,2] 10)
  putStrLn ""

  putStrLn "  [1,2,4,8,16,32] target=21 (YES, super-increasing):"
  putStr $ showCoupledStats (coupledBitSolve [1,2,4,8,16,32] 21)
  putStrLn ""

  putStrLn "  [1,2,3,5,8] target=10 (YES, Fibonacci):"
  putStr $ showCoupledStats (coupledBitSolve [1,2,3,5,8] 10)
  putStrLn ""

  sectionHeader "30. UNTIE-RETIE: decouple, solve easy, re-check coupling"
  putStrLn "  Can we solve the uncoupled (easy) problem and then filter"
  putStrLn "  for coupled solutions? How many subsets survive the filter?"
  putStrLn ""

  putStrLn "  [3,7,5,2] target=10 (YES, 2 solutions):"
  putStr $ showUntieRetie (untieRetieExperiment [3,7,5,2] 10)
  putStrLn ""

  putStrLn "  [3,7,5,2] target=11 (NO):"
  putStr $ showUntieRetie (untieRetieExperiment [3,7,5,2] 11)
  putStrLn ""

  putStrLn "  [1,2,4,8,16,32] target=21 (YES, super-increasing):"
  putStr $ showUntieRetie (untieRetieExperiment [1,2,4,8,16,32] 21)
  putStrLn ""

  putStrLn "  [1,2,3,5,8,13] target=15 (YES):"
  putStr $ showUntieRetie (untieRetieExperiment [1,2,3,5,8,13] 15)
  putStrLn ""

  putStrLn "  Survival rate = P(random subset hits target)."
  putStrLn "  If survival rate is 1/poly(n) → retie is easy."
  putStrLn "  If survival rate is 1/2^n → retie is as hard as brute force."
  putStrLn ""

  sectionHeader "31. INTERLEAVED: carry + coupling at EACH bit position"
  putStrLn "  Process bit-by-bit, carrying coupling decisions forward."
  putStrLn "  active(k) = weights decided at k with future bits remaining."
  putStrLn "  State = carry × 2^active(k). If active is small → poly!"
  putStrLn ""

  putStrLn "  [3,7,5,2] target=10:"
  putStr $ showInterleavedStats (interleavedSolve [3,7,5,2] 10)
  putStrLn ""

  putStrLn "  [1,2,4,8,16,32] target=21 (super-increasing):"
  putStr $ showInterleavedStats (interleavedSolve [1,2,4,8,16,32] 21)
  putStrLn ""

  putStrLn "  [1,2,3,5,8,13] target=15 (fibonacci):"
  putStr $ showInterleavedStats (interleavedSolve [1,2,3,5,8,13] 15)
  putStrLn ""

  putStrLn "  [100,200,400,800,1600] target=1000 (exponential weights):"
  putStr $ showInterleavedStats (interleavedSolve [100,200,400,800,1600] 1000)
  putStrLn ""

  sectionHeader "32. BASIS SEARCH: can multiplying reduce overlap?"
  putStrLn "  Multiplying weights by c redistributes bits."
  putStrLn "  Does any c reduce max_active?"
  putStrLn ""

  putStrLn "  Dense overlap: [3,5,7] (all odd → bit 0 overlap = 3):"
  putStr $ showBasisSearch [3,5,7] 20
  putStrLn ""

  putStrLn "  Fibonacci: [1,2,3,5,8,13]:"
  putStr $ showBasisSearch [1,2,3,5,8,13] 20
  putStrLn ""

  putStrLn "  Dense: [7,11,13,14] (lots of shared bits):"
  putStr $ showBasisSearch [7,11,13,14] 20
  putStrLn ""

  sectionHeader "33. GF(2) TRANSFORMS: non-linear overlap reduction"
  putStrLn "  Linear multiplication can't reduce overlap. But XOR-based"
  putStrLn "  transforms (mixing bits) are NON-LINEAR and might help."
  putStrLn ""

  putStrLn "  [3,5,7] (all odd, overlap=3 at bit 0):"
  putStr $ showGF2Results [3,5,7]
  putStrLn ""

  putStrLn "  [1,2,3,5,8,13] (fibonacci):"
  putStr $ showGF2Results [1,2,3,5,8,13]
  putStrLn ""

  putStrLn "  [7,11,13,14] (dense binary):"
  putStr $ showGF2Results [7,11,13,14]
  putStrLn ""

  putStrLn "  [3,5,6,7] (very dense):"
  putStr $ showGF2Results [3,5,6,7]
  putStrLn ""

  sectionHeader "34. SOLVING in GF(2)-transformed basis"
  putStrLn "  Transform weights to reduce overlap, then run interleaved"
  putStrLn "  solver on transformed weights. Does it use fewer states?"
  putStrLn ""

  putStrLn "  [3,5,7] target=8 (YES: 3+5):"
  putStr $ showGF2SolverResult (solveInTransformedBasis [3,5,7] 8)
  putStrLn ""

  putStrLn "  [3,5,7] target=6 (NO):"
  putStr $ showGF2SolverResult (solveInTransformedBasis [3,5,7] 6)
  putStrLn ""

  putStrLn "  [1,2,3,5,8,13] target=15 (YES):"
  putStr $ showGF2SolverResult (solveInTransformedBasis [1,2,3,5,8,13] 15)
  putStrLn ""

  putStrLn "  [3,5,6,7] target=11 (YES: 5+6):"
  putStr $ showGF2SolverResult (solveInTransformedBasis [3,5,6,7] 11)
  putStrLn ""

  sectionHeader "35. GF(2) RANK: how much CAN overlap be reduced?"
  putStrLn "  If rank = n → overlap can reach 0 (diagonal form)"
  putStrLn "  If rank < n → some overlap is unavoidable"
  putStrLn ""

  putStrLn "  [3,5,7]:"
  putStr $ showRankAnalysis (analyzeRank [3,5,7])
  putStrLn ""

  putStrLn "  [1,2,3,5,8,13]:"
  putStr $ showRankAnalysis (analyzeRank [1,2,3,5,8,13])
  putStrLn ""

  putStrLn "  [1,2,4,8,16,32] (super-increasing):"
  putStr $ showRankAnalysis (analyzeRank [1,2,4,8,16,32])
  putStrLn ""

  putStrLn "  [3,5,6,7,9,10,11] (7 dense weights):"
  putStr $ showRankAnalysis (analyzeRank [3,5,6,7,9,10,11])
  putStrLn ""

  putStrLn "  [7,11,13,14,15] (very dense 4-bit):"
  putStr $ showRankAnalysis (analyzeRank [7,11,13,14,15])
  putStrLn ""

  sectionHeader "36. RECURSIVE GF(2): carry correction as Writer monad"
  putStrLn "  Strip highest bit → solve easy part → corrections are SMALLER"
  putStrLn "  Recurse on corrections. Each level removes 1 bit."
  putStrLn "  KEY: how many distinct correction sums at each level?"
  putStrLn ""

  putStrLn "  [3,5,7] target=8 (YES: 3+5):"
  putStr $ showRecursiveResult (recursiveGF2Solve [3,5,7] 8)
  putStrLn ""

  putStrLn "  [1,2,3,5,8,13] target=15 (YES):"
  putStr $ showRecursiveResult (recursiveGF2Solve [1,2,3,5,8,13] 15)
  putStrLn ""

  putStrLn "  [1,2,4,8,16,32] target=21 (YES, super-increasing):"
  putStr $ showRecursiveResult (recursiveGF2Solve [1,2,4,8,16,32] 21)
  putStrLn ""

  putStrLn "  [3,5,6,7,9,10,11] target=20 (YES):"
  putStr $ showRecursiveResult (recursiveGF2Solve [3,5,6,7,9,10,11] 20)
  putStrLn ""

  sectionHeader "37. SCALING: do corrections stay polynomial?"
  putStrLn "  THE critical experiment. If max corrections = O(poly(n))"
  putStrLn "  for ALL instances → P = NP. If exponential → P /= NP."
  putStrLn ""
  putStrLn "  n    weights             DP sums  max corr  levels  ratio"
  putStrLn $ "  " ++ replicate 65 '-'

  let scalingTests =
        [ [1,2,3]                               -- n=3
        , [1,2,3,5]                              -- n=4
        , [1,2,3,5,8]                            -- n=5
        , [1,2,3,5,8,13]                         -- n=6
        , [1,2,3,5,8,13,21]                      -- n=7
        , [1,2,3,5,8,13,21,34]                   -- n=8
        , [3,5,7,9,11,13]                        -- n=6 odd
        , [3,5,7,9,11,13,15,17]                  -- n=8 odd
        , [3,5,6,7,9,10,11]                      -- n=7 dense
        , [3,5,6,7,9,10,11,13,14,15]             -- n=10 dense
        , [1,2,4,8,16,32,64]                     -- n=7 super-inc
        , [1,2,4,8,16,32,64,128]                 -- n=8 super-inc
        , [1,2,4,8,16,32,64,128,256]             -- n=9 super-inc
        , [1,2,4,8,16,32,64,128,256,512]         -- n=10 super-inc
        ]

  mapM_ (\ws -> do
    let t = sum ws `div` 2 + 1  -- target ≈ half sum + 1 (likely NO)
        rr = recursiveGF2Solve ws t
        dp = rrDPSize rr
        mc = rrMaxCorrections rr
        lv = rrLevels rr
        ratio' = if mc > 0 then fromIntegral dp / fromIntegral mc else 0 :: Double
    putStrLn $ "  " ++ padRight 5 (show (length ws))
            ++ padRight 20 (show ws)
            ++ padRight 9 (show dp)
            ++ padRight 10 (show mc)
            ++ padRight 8 (show lv)
            ++ show (round ratio' :: Int) ++ "x"
    ) scalingTests

  putStrLn ""
  putStrLn "  If ratio grows with n → corrections shrink faster than DP"
  putStrLn "  If ratio stays constant → same complexity class"
  putStrLn "  If ratio shrinks → corrections grow FASTER (bad)"
  putStrLn ""

  sectionHeader "38. COMPOUNDING? Per-level correction sizes"
  putStrLn "  For complexity class change, each level must REDUCE corrections"
  putStrLn "  by a multiplicative factor (not just the first level)."
  putStrLn ""

  let detailedTests =
        [ ([3,5,7], 6)
        , ([1,2,3,5,8,13], 15)
        , ([3,5,6,7,9,10,11], 20)
        , ([3,5,6,7,9,10,11,13,14,15], 48)
        , ([3,5,7,9,11,13,15,17], 40)
        , ([1,2,3,5,8,13,21,34], 44)
        , ([3,5,6,7,9,10,11,12,13,14,15], 55)
        ]

  mapM_ (\(ws, t) -> do
    let rr = recursiveGF2Solve ws t
    putStrLn $ "  n=" ++ show (length ws) ++ " " ++ show ws ++ " t=" ++ show t
    putStrLn $ "    DP sums: " ++ show (rrDPSize rr)
    putStrLn $ "    Corrections/level: " ++ show (rrCorrectionSizes rr)
    putStrLn $ "    Weights/level:"
    mapM_ (\(i, ws') ->
      putStrLn $ "      L" ++ show i ++ ": "
              ++ show (filter (/= 0) ws')
              ++ " (" ++ show (length (filter (/= 0) ws')) ++ " non-zero)"
      ) (zip [(0::Int)..] (rrWeightsPerLevel rr))
    -- Check compounding: does each level reduce by a factor?
    let sizes = rrCorrectionSizes rr
        ratios = zipWith (\a b -> if b > 0 then fromIntegral a / fromIntegral b else 0 :: Double)
                         sizes (tail sizes)
    putStrLn $ "    Level-to-level ratios: " ++ show (map (\r -> fromIntegral (round (r * 10) :: Int) / 10) ratios)
    putStrLn $ "    " ++ if all (> 1.5) ratios && length ratios > 1
                         then "COMPOUNDING! Each level reduces corrections."
                         else if any (> 1.5) ratios
                         then "Partial compounding (some levels reduce)."
                         else "No compounding — same rate."
    putStrLn ""
    ) detailedTests

  sectionHeader "39. LARGE SCALE: level-0 corrections vs n (n=5..20)"
  putStrLn "  If level-0 corrections = O(n) → total is polynomial."
  putStrLn "  If level-0 corrections = O(2^n) → still exponential."
  putStrLn ""
  putStrLn "  n    type        DP sums  L0 corr  L0/n   L0/DP"
  putStrLn $ "  " ++ replicate 55 '-'

  -- Dense: consecutive odd numbers [3,5,7,...,2n+1]
  let denseN n = [2*i+1 | i <- [1..n]]
  -- Fibonacci
  let fibN n = take n $ drop 2 fibs where fibs = 0 : 1 : zipWith (+) fibs (tail fibs)
  -- Random-ish: primes
  let primeN n = take n [p | p <- [2..], isPrime p]
      isPrime p = p > 1 && all (\d -> p `mod` d /= 0) [2..floor (sqrt (fromIntegral p) :: Double)]

  mapM_ (\(name, gen) ->
    mapM_ (\n -> do
      let ws = gen n
          t = sum ws `div` 2 + 1
          rr = recursiveGF2Solve ws t
          dp = rrDPSize rr
          l0 = if null (rrCorrectionSizes rr) then 0 else head (rrCorrectionSizes rr)
          l0n = if n > 0 then fromIntegral l0 / fromIntegral n else 0 :: Double
          l0dp = if dp > 0 then fromIntegral l0 / fromIntegral dp else 0 :: Double
      putStrLn $ "  " ++ padRight 5 (show n)
              ++ padRight 12 name
              ++ padRight 9 (show dp)
              ++ padRight 9 (show l0)
              ++ padRight 7 (show (roundTo' 1 l0n))
              ++ show (roundTo' 3 l0dp)
      ) [5,8,10,12,14,16,18,20]
    ) [ ("dense", denseN)
      , ("fibonacci", fibN)
      , ("primes", primeN)
      ]

  putStrLn ""
  putStrLn "  L0/n = level-0 corrections per element."
  putStrLn "  If L0/n stays CONSTANT → L0 = O(n) → POLYNOMIAL!"
  putStrLn "  If L0/n grows → L0 = super-linear → check rate."
  putStrLn ""

  sectionHeader "40. RANDOM GF(2) VOTE: probabilistic algorithm"
  putStrLn "  Apply N random GF(2) transforms, solve each, majority vote."
  putStrLn "  If P(false positive) < 0.5 for NO instances → BPP algorithm!"
  putStrLn ""

  let voteTrials = 50

  putStrLn "  YES instances (should all say YES):"
  putStr $ showVoteResult (randomGF2Vote voteTrials [3,5,7] 8)
  putStr $ showVoteResult (randomGF2Vote voteTrials [1,2,3,5,8,13] 15)
  putStr $ showVoteResult (randomGF2Vote voteTrials [3,5,6,7,9,10,11] 20)
  putStrLn ""

  putStrLn "  NO instances (THE KEY: what's the false positive rate?):"
  putStr $ showVoteResult (randomGF2Vote voteTrials [3,5,7] 6)
  putStr $ showVoteResult (randomGF2Vote voteTrials [3,5,7] 11)
  putStr $ showVoteResult (randomGF2Vote voteTrials [1,2,3,5,8,13] 33)
  putStr $ showVoteResult (randomGF2Vote voteTrials [3,5,6,7,9,10,11] 62)
  putStr $ showVoteResult (randomGF2Vote voteTrials [1,2,4,8,16,32] 50)
  putStrLn ""

  putStrLn "  If ALL FP rates < 0.5 → majority vote always correct"
  putStrLn "  → Subset Sum ∈ BPP → likely P = NP"
  putStrLn ""

  sectionHeader "41. DISTRIBUTIVE: Schwartz-Zippel on g(x)/x^T"
  putStrLn "  g(α)*α^(-T) mod p is O(n) per evaluation."
  putStrLn "  If [x^T]g(x) ≠ 0, then g(α)*α^(-T) ≠ 0 with high prob."
  putStrLn "  Test: for YES instances with small prime p, does it detect?"
  putStrLn ""

  let szEval ws t p alpha =
        let gAlpha = foldl (\acc w -> (acc * ((1 + modPow p alpha w) `mod` p)) `mod` p) 1 ws
            invAlphaT = modPow p alpha (p - 1 - (t `mod` (p-1)))
        in (gAlpha * invAlphaT) `mod` p

  let szTest ws t p = do
        let results = [szEval ws t p alpha | alpha <- [2..p-1]]
            nonzero = length (filter (/= 0) results)
            total = length results
            rate = fromIntegral nonzero / fromIntegral (max 1 total) :: Double
        putStrLn $ "    p=" ++ padRight 6 (show p)
                ++ "nonzero: " ++ padRight 8 (show nonzero ++ "/" ++ show total)
                ++ "rate: " ++ show (roundTo' 2 rate)

  putStrLn "  [3,5,7] target=8 (YES: 3+5=8):"
  mapM_ (szTest [3,5,7] 8) [7, 11, 13, 17, 23, 31, 97]
  putStrLn ""

  putStrLn "  [1,2,3,5,8,13] target=15 (YES):"
  mapM_ (szTest [1,2,3,5,8,13] 15) [17, 23, 31, 97]
  putStrLn ""

  putStrLn "  [3,5,7] target=6 (NO — should be ALL zero):"
  mapM_ (szTest [3,5,7] 6) [7, 11, 13, 17, 23, 31, 97]
  putStrLn ""

  -- Phase J: LLL + density + topology + combined
  sectionHeader "42. LLL Lattice Reduction"
  putStrLn "  LLL solves Subset Sum in POLYNOMIAL time for low density."
  putStrLn ""
  putStrLn "  Low density: [389, 769, 1543] target=1350:"
  putStr $ showLLLResult (lllSolve [389, 769, 1543] 1350)
  putStrLn ""
  putStrLn "  Medium density: [3,5,7,9,11] target=20:"
  putStr $ showLLLResult (lllSolve [3,5,7,9,11] 20)
  putStrLn ""

  sectionHeader "43. Gap topology (non-algebrizing approach)"
  putStrLn "  Gaps in reachable sums have NON-ALGEBRAIC structure."
  putStrLn ""
  putStr $ showGapAnalysis (analyzeGaps [1,2,3,5,8,13])
  putStrLn ""
  putStr $ showGapAnalysis (analyzeGaps [3,5,7,9,11,13])
  putStrLn ""
  putStr $ showGapAnalysis (analyzeGaps [6,10,15,21,28])
  putStrLn ""

  sectionHeader "44. Density sweep: which method works where?"
  putStr $ showDensitySweep (densitySweep 8)
  putStrLn ""

  sectionHeader "45. Combined solver: mapping the DEAD ZONE"
  let combinedTests =
        [ ([389, 769, 1543], 1350)           -- low density
        , ([3,5,7,9,11,13], 25)              -- high density
        , ([1,2,3,5,8,13,21,34], 44)         -- medium density (Fibonacci)
        , ([100,200,400,800,1600], 1000)      -- exponential weights
        , ([3,5,6,7,9,10,11,13,14,15], 48)   -- dense
        ]
  mapM_ (\(ws, t) -> putStrLn $ showCombinedResult (combinedSolve ws t)) combinedTests
  putStrLn ""

  sectionHeader "46. DEAD ZONE HUNT: density ≈ 1"
  putStrLn "  Critical regime: n ≈ log2(max_weight)."
  putStrLn "  Testing with n=6,7,8 and weights ≈ 2^n."
  putStrLn ""

  -- Density ≈ 1: weights around 2^n, so n ≈ log2(max)
  let criticalTests =
        -- n=6, weights ≈ 64 → density ≈ 1.0
        [ ([37, 41, 43, 47, 53, 59], 150)      -- NO
        , ([37, 41, 43, 47, 53, 59], 137)      -- YES: 37+41+59
        -- n=7, weights ≈ 128 → density ≈ 1.0
        , ([97, 103, 107, 109, 113, 127, 131], 400)  -- NO
        , ([97, 103, 107, 109, 113, 127, 131], 329)  -- YES
        -- n=8, weights ≈ 256 → density ≈ 1.0
        , ([197, 199, 211, 223, 227, 229, 233, 239], 1000) -- NO
        , ([197, 199, 211, 223, 227, 229, 233, 239], 857)  -- YES
        -- n=8, all primes near 256
        , ([241, 251, 257, 263, 269, 271, 277, 281], 1300) -- NO
        , ([241, 251, 257, 263, 269, 271, 277, 281], 1100) -- prob YES
        ]

  putStrLn "  n    density  DP      LLL  strm   ovlp  gap    method"
  putStrLn $ "  " ++ replicate 65 '-'
  mapM_ (\(ws, t) -> putStrLn $ showCombinedResult (combinedSolve ws t)) criticalTests
  putStrLn ""

  putStrLn "  DEAD ZONE = instances where method = 'DEAD ZONE'"
  putStrLn ""

  sectionHeader "47. REAL DEAD ZONE HUNT: n=10, mixed parity, density ≈ 1"
  putStrLn "  Mixed even/odd weights ≈ 2^10, no structure, density ≈ 1."
  putStrLn "  Using FAST methods only (DP reachable + streaming + overlap)."
  putStrLn ""

  -- n=10, weights ≈ 1024, mixed parity — density ≈ 1
  let hunt ws t tag = do
        let cr = combinedSolve ws t
            n = length ws
            peak = crStreamPeak cr
            dpSize = crDPSize cr
            overlap = crGF2Overlap cr
            deadZone = peak > n * n && dpSize > n * n && overlap > n `div` 2
        putStrLn $ "  " ++ padRight 9 tag
                ++ " d=" ++ padRight 5 (show (roundTo' 1 (crDensity cr)))
                ++ " DP=" ++ padRight 6 (show dpSize)
                ++ " strm=" ++ padRight 5 (show peak)
                ++ " ovl=" ++ padRight 3 (show overlap)
                ++ " sol=" ++ padRight 4 (if crCorrectAns cr then "YES" else "NO")
                ++ (if deadZone then " ← DEAD ZONE!" else " → " ++ crMethod cr)

  hunt [502, 757, 1018, 543, 876, 691, 1234, 419, 800, 663] 4200 "mix10a"
  hunt [502, 757, 1018, 543, 876, 691, 1234, 419, 800, 663] 3775 "mix10a'"
  hunt [612, 939, 1107, 458, 723, 1051, 834, 567, 1190, 401] 5100 "mix10b"
  hunt [612, 939, 1107, 458, 723, 1051, 834, 567, 1190, 401] 4539 "mix10b'"
  hunt [410, 623, 1087, 544, 891, 722, 1150, 367, 956, 508] 3800 "mix10c"
  hunt [802, 515, 1233, 678, 944, 1101, 456, 789, 1067, 630] 4600 "mix10d"
  -- Smaller: n=8 with density exactly 1
  hunt [130, 200, 172, 255, 198, 143, 210, 187] 750 "mix8a"
  hunt [130, 200, 172, 255, 198, 143, 210, 187] 900 "mix8b"
  putStrLn ""
  putStrLn "  DEAD ZONE = strm > n² AND DP > n² AND overlap > n/2"
  putStrLn ""

  putStrLn "═══════════════════════════════════════════════════════════"
  putStrLn " PROJECT SUMMARY (Phases A-J)"
  putStrLn " A-C: Enriched categories, BF, DP, SAT connection"
  putStrLn " D: Monoid homomorphisms → pigeonhole barrier"
  putStrLn " F: Myhill-Nerode, reachability → same barrier"
  putStrLn " G: Polynomial ring → no improvement over ZMod"
  putStrLn " H: LP relaxation → integrality gap"
  putStrLn " I: Lazy pruning, streaming, diagonalization"
  putStrLn " All roads lead to the same invariant: distinct sums."
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
