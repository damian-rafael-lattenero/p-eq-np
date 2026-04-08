import PeqNP.MultiLevelSieve
import qualified Data.Set as Set

main :: IO ()
main = do
  putStrLn "=== FULL VERIFICATION: rRec vs 2-level, many targets ==="
  putStrLn ""
  mapM_ verifyN [8,10,12,14,16]

verifyN :: Int -> IO ()
verifyN n = do
  let (ws, _) = mkDensity1 n
      dp = foldl (\s w -> Set.union s (Set.map (+w) s)) (Set.singleton 0) ws
      yesTs = take 10 $ Set.toList $ filterRange (sum ws `div` 4) (sum ws * 3 `div` 4) dp
      noTs = take 10 [t | t <- [sum ws `div` 4..sum ws * 3 `div` 4], not (Set.member t dp)]
      allTs = [(t, True) | t <- yesTs] ++ [(t, False) | t <- noTs]

  let results = [ (dpAns, srFound (multiLevelSolve 2 ws t), srFound (recursiveRepSolve 4 ws t))
                | (t, dpAns) <- allTs ]
      err2 = length [() | (d, s, _) <- results, d /= s]
      errR = length [() | (d, _, r) <- results, d /= r]

  putStrLn $ "n=" ++ show n ++ ": " ++ show (length allTs) ++ " targets"
    ++ "  2-level errors=" ++ show err2
    ++ "  rRec errors=" ++ show errR
    ++ (if err2 == 0 && errR == 0 then "  ✓ ALL OK" else "  ✗")

  -- Show errors if any
  mapM_ (\(dpAns, s2, sR) ->
    if dpAns /= s2 || dpAns /= sR
    then putStrLn $ "  dp=" ++ show dpAns ++ " 2lvl=" ++ show s2 ++ " rRec=" ++ show sR
    else return ()
    ) results

filterRange :: Int -> Int -> Set.Set Int -> Set.Set Int
filterRange lo hi s =
  let (_, geq) = Set.split (lo-1) s
      (leq, _) = Set.split (hi+1) geq
  in leq
