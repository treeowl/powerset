{- OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -O #-}

module Main (main) where
import PowerSet
import System.Environment
-- import GHC.Exts (toList)
import Data.Set.Internal (valid)
import qualified Data.Set as S
import Data.Set (fromList, Set)
import Data.Foldable
import Control.Exception

main :: IO ()
main = do
  --[ns] <- getArgs
  --let n :: Int
  --    n = read ns
  --print . length $ [x | outer <- izoop n, inner <- outer, x <- ilToList inner]
  --print . length $ [x | outer <- zum n, inner <- outer, x <- inner]
  --print $ sum [ilLength inner | outer <- izoop n, inner <- outer]
  --print . length $ [x | xs <- zoopA (mkPascal (n - 1)) n, ys <- xs, x <- toList ys]
--  for_ [22] $ print . test1
  let s = fromList [1..24]
  evaluate (powerSet s)
  putStrLn "Done"
{-
  for_ [0..20] $ \n -> do
    let s = fromList [1..n]
    print $ S.difference (powerSet s) (S.powerSet s)
    -}
--    print . fmap toList . toList $ S.powerSet s
--    print . fmap toList . toList $ powerSet s


test1 :: Int -> Bool
test1 n = valid ps {- && all valid ps -} && ps == S.powerSet s
  where
    s = fromList [1..n]
    ps = powerSet s

test2 :: Int -> Set (Set Int)
test2 n = powerSet $ fromList [1..n]
