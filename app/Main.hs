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

  putStrLn "═══════════════════════════════════════════════════════════"

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
