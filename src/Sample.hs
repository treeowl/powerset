module Sample where

import Data.Set (Set, powerSet, size)
import qualified Data.Set as S

printStratified :: Show a => [(Int, Set a)] -> IO ()
printStratified = mapM_ $
  \(line, s) ->
    let indent = replicate (6 * size s) ' '
    in putStrLn $ extend 3 (show line) ++ indent ++ show (S.toList s)

run :: Int -> IO ()
run n = printStratified $ zip [0..] $ S.toList $ powerSet $ S.fromList [0..n-1::Int]

extend :: Int -> String -> String
extend n s = take n (s ++ repeat ' ')
