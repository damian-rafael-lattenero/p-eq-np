import PeqNP.MultiLevelSieve
import qualified Data.Set as Set

main :: IO ()
main = do
  putStrLn "=== rRec BENCHMARK (the ONLY 100% correct solver) ==="
  putStrLn "n     rRec4    rRec8    MITM     ratio4  ratio8  ok"
  putStrLn (replicate 60 '-')
  mapM_ run [8,10,12,14,16,18,20,22,24]

run :: Int -> IO ()
run n = do
  let (ws, t) = mkDensity1 n
      mitm = 3 * 2^(n `div` 2) :: Int
      sr4 = recursiveRepSolve 4 ws t
      sr8 = recursiveRepSolve 8 ws t
      r4 = fromIntegral mitm / fromIntegral (max 1 (srWork sr4)) :: Double
      r8 = fromIntegral mitm / fromIntegral (max 1 (srWork sr8)) :: Double
  putStrLn $ pad 6 (show n)
    ++ pad 9 (show (srWork sr4)) ++ pad 9 (show (srWork sr8))
    ++ pad 9 (show mitm)
    ++ pad 8 (show (rnd r4)) ++ pad 8 (show (rnd r8))
    ++ (if srCorrect sr4 && srCorrect sr8 then "✓" else "✗")

pad n s = s ++ replicate (max 0 (n - length s)) ' '
rnd x = fromIntegral (round (x * 10 :: Double) :: Int) / 10
