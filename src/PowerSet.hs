{-  options_ghc -ddump-simpl #-}
{- options_ghc -ddump-stg-from-core #-}
{- options_ghc -ddump-cmm #-}
{-# language UnboxedTuples #-}
{-# language BangPatterns #-}
{-# language MagicHash #-}
{-# language ViewPatterns #-}
{-# language ScopedTypeVariables #-}
{-# language DeriveFoldable #-}
{-# language StandaloneDeriving #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
-- {-# language OverloadedLists #-}
{-# options_ghc -Wno-unused-imports #-}
module PowerSet where

import Data.Set.Internal (Set (..), bin)
import qualified Data.Set as S
import Data.Primitive.Array (Array, indexArray##)
import qualified Data.Primitive.Array as A
import qualified GHC.Exts as E
import qualified Data.Primitive.PrimArray as PA
import Data.Primitive.PrimArray (PrimArray)
import Data.Word (Word8)
import Control.Monad.ST
import Data.Primitive (Prim)
import GHC.Stack
import qualified Data.Foldable as F
import qualified Data.Sequence as EQ (Seq, (<|), (|>), viewl, ViewL (..), fromList)
import qualified Data.List as List
import Debug.Trace

powerSet :: Set a -> Set (Set a)
-- We start off with special cases for tiny sets. Why?
--
-- 1. The column construction function uses columns with sets of size 1 and 2
-- as base cases, so we need special functions to construct those columns.
-- Having both array and list-producing forms of those functions seems a bit
-- silly; once the underlying set has at least 4 elements, we only need the
-- array versions, so we just sidestep by generating the powerset by hand for
-- smaller sets.
--
-- 2. While the array tableau seems like reasonable overhead when dealing with
-- most sets, it's hard to justify its expense for the very tiniest ones.
--
-- 3. A side benefit: building the subsets by hand lets us take full advantage
-- of the structure of the argument set, reducing memory use to an absolute
-- bare minimum. This benefit tends to insignificance as the set size
-- increases.
powerSet Tip = S.singleton Tip
powerSet s@(Bin 1 _ _ _) =
  -- It would be slightly faster to search the result if we put the Tip at the
  -- root, but that would force us to allocate an extra Bin constructor. As written,
  -- singleton Tip is floated out to the top level and shared globally.
  Bin 2 s (S.singleton Tip) Tip
powerSet s@(Bin 2 a Tip sing_b) =
  Bin 4 (S.singleton a)
        (S.singleton Tip)
        (Bin 2 sing_b (S.singleton s) Tip)
powerSet s@(Bin 2 b sing_a Tip) =
  Bin 4 sing_a
        (S.singleton Tip)
        (Bin 2 (S.singleton b) (S.singleton s) Tip)
-- Note: a set with 3 elements can only have one shape!
powerSet s@(Bin 3 b sing_a@(Bin _ a _ _) sing_c) =
  Bin 8 (S.singleton b)
    (Bin 5 sing_a
           (S.singleton Tip)
           (Bin 3 s (S.singleton (Bin 2 b sing_a Tip)) (S.singleton (Bin 2 a Tip sing_c))))
    (Bin 2 sing_c (S.singleton (Bin 2 b Tip sing_c)) Tip)
-- If we want, we can construct power sets "manually" for sets of slightly larger sizes,
-- but the amount of manual labor rises rapidly and the benefits drop off quickly. We might
-- want to consider switching over to Soumik Sarkar's algorithm for sizes between 4 and
-- wherever its intermediate allocation costs overtake the costs of the main algorithm.
powerSet s = S.fromDistinctAscList $ bigMerge (S.size s) (columnTable (arrayFromListN (S.size s) (F.toList s)))



data Column a
  = ColumnArr !(Array (Array (Set a)))
  | ColumnLst [Set a]
  deriving Show

columnToList :: Column a -> [Set a]
columnToList (ColumnLst ss) = ss
columnToList (ColumnArr ary) =
  [ s
  | inner <- arrayToListEager ary
  , s <- F.toList inner
  ]

-- Just for testing
isArr :: Column a -> Bool
isArr (ColumnArr _) = True
isArr (ColumnLst _) = False

columnTable :: Array a -> [[Set a]]
columnTable = fmap columnToList . columnTable'

-- Split out for testing
columnTable' :: Array a -> [Column a]
columnTable' els = take sz_underlying columns
  where
    columns = ColumnArr c1 : ColumnArr c2 : go 1 allMaxima columns
    allMaxima = zoopA pasc sz_underlying
    pasc = mkPascal (sz_underlying - 1)
    sz_underlying = A.sizeofArray els
    c1 = column1 els
    c2 = column2 els c1
    go szA (maxesA : maxes) (ColumnArr arA : cs'@(cb : _)) = case cb of
      ColumnArr arB
        -> condCombine pasc szA arA maxesA els szA arA :
           condCombine pasc szA arA maxesA els (szA + 1) arB :
           go (szA + 1) maxes cs'
      ColumnLst _
        -> [ColumnLst (combine3 szA arA maxesA els szA arA)]
    go _ _ _ = []


condCombine
  :: Pascal
  -> Int -- Size of left subtrees
  -> Array (Array (Set a)) -- Left subtrees
  -> Array (PrimArray Word8) -- Maximal indices of left subtrees
  -> Array a -- elements
  -> Int -- Size of right subtrees
  -> Array (Array (Set a)) -- Right subtrees
  -> Column a
condCombine pasc sz_left lefts maxes els sz_right rights 
  | sz_left + sz_right + 1 <= A.sizeofArray els `quot` 2
  = ColumnArr (combine3A pasc sz_left lefts maxes els sz_right rights)
  | otherwise
  = ColumnLst (combine3 sz_left lefts maxes els sz_right rights)


data Zipper a = Zipper [a] a [a]

bigMerge :: Int -> [[Set a]] -> [Set a]
bigMerge n columns = go (Zipper [] [S.empty] columns) (enddir n)
  where
    go :: Zipper [Set a] -> SmallerBigger -> [Set a]
    go (Zipper _ [] _) _ = []
    go (Zipper ls (s : ss) rs) ds
      = s : case ds of
          Smaller ds' -> case ls of
            [] -> []
            l : ls' -> go (Zipper ls' l (ss : rs)) ds'
          Bigger ds' -> case rs of
            [] -> []
            r : rs' -> go (Zipper (ss : ls) r rs') ds'
          NoMore -> error "Ran out of directions"

data SmallerBigger
  = Smaller SmallerBigger
  | Bigger SmallerBigger
  | NoMore
  deriving Show

enddir :: Int -> SmallerBigger
enddir n0 = Bigger $ ends' n0 NoMore
  where
    ends' 1 = Smaller
    ends' n = Bigger . ends' (n - 1) . ends' (n - 1)

data IL
  = !Int :# IL
  | INil

ilLength :: IL -> Int
ilLength = go 0
  where
    go acc INil = acc
    go acc (_ :# r) = go (acc + 1) r

ilToList :: IL -> [Int]
ilToList (i :# il) = i : ilToList il
ilToList INil = []

instance Show IL where
  showsPrec p = showsPrec p . ilToList

map' :: (a -> b) -> [a] -> [b]
map' f xs = E.build $ \c n ->
  foldr (\a r -> let !b = f a in b `c` r) n xs

izoop :: Int -> [[IL]]
izoop n = List.map (List.map ($ INil)) . zap . map' (:#) $ [1..n]
  where
    zap :: [IL -> IL] -> [[IL -> IL]]
    zap [] = []
    zap s@(_ : xs) = s : zap (List.map (List.foldr (.) id) (List.init $ List.tails xs))

zoop :: Int -> [[[Int]]]
zoop n = List.map (List.map ($ [])) . zap . List.map (:) $ [1..n]
  where
    zap :: [[a] -> [a]] -> [[[a] -> [a]]]
    zap [] = []
    zap s@(_ : xs) = s : zap (List.map (List.foldr (.) id) (List.init $ List.tails xs))

-- This is a more space-efficient alternative to arrays of maximal indices.
-- If traversing trees of indices is too expensive, another option would be to
-- compromise by using trees of arrays.
data Tree a
  = Branch !(Tree a) !(Tree a)
  | Leaf a
  deriving (Show) -- , Foldable)

instance Foldable Tree where
  foldMap f = go
    where
      go (Leaf a) = f a
      go (Branch l r) = go l <> go r
  foldr c = go
    where
      go n (Leaf a) = a `c` n
      go n (Branch l r) = go (go n r) l
  null _ = False

zum :: Int -> [[[Int]]]
zum = fmap (fmap F.toList) . zoobby

zoobby :: Int -> [[Tree Int]]
zoobby n = zap . fmap Leaf $ [0..n-1]
  where
    zap :: [Tree Int] -> [[Tree Int]]
    zap [] = []
    zap s@(_ : xs) = s : zap (fmap (List.foldr1 Branch) (List.init $ List.tails xs))

-- A version of zoobby that produces arrays. This is very fast, but the arrays use much
-- more memory than trees. Still, it's a small fraction of the total space, so it might
-- be better.
zoopA :: Pascal -> Int -> [Array (PrimArray Word8)]
zoopA pasc n = map A.arrayFromList . zap 1 . map' (PA.primArrayFromListN 1 . pure . fromIntegral) $ [0..n-1]
  where
    -- The first argument is the column number (size of sets in column)
    zap :: Int -> [PrimArray Word8] -> [[PrimArray Word8]]
    zap !_ [] = []
    zap !cn s@(_ : xs) = s : zap (cn + 1)
          (imap (\start -> concatA (arrSize pasc n (cn + 1) start)) (List.init $ List.tails xs))

{-
arrSize :: Pascal -> Int -> Int -> Int -> Int
arrSize pasc set_size subset_size first_ix
  = comb pasc (set_size - first_ix - 1) (subset_size - 1)
-}

-- concatA takes a list of arrays and their total size, and produces
-- an array with the contents of all of them.
concatA :: forall a. Prim a => Int -> [PrimArray a] -> PrimArray a
concatA tots ars = runST run where
  run :: forall s. ST s (PrimArray a)
  run = do
    ma <- PA.newPrimArray tots
    let
      go :: PrimArray a -> (Int -> ST s ()) -> Int -> ST s ()
      go a r !ix
        | ix + sz_a <= tots
        = do
            PA.copyPrimArray ma ix a 0 sz_a
            r (ix + sz_a)
        | otherwise
        = die "concatA: Total length greater than specified size"
        where
          !sz_a = PA.sizeofPrimArray a
      stop :: Int -> ST s ()
      stop ix
        | ix == tots
        = pure ()
        | otherwise
        = die "concatA: total length less than specified size"
    foldr go stop ars 0
    PA.unsafeFreezePrimArray ma

column1 :: Array a -> Array (Array (Set a))
column1 els = arrayFromListN (A.sizeofArray els)
  [ s
  | x <- F.toList els
  , let !s = pure $! S.singleton x
  ]

column2
  :: Array a -- Underlying set
  -> Array (Array (Set a)) -- Column 1
  -> Array (Array (Set a))
column2 els c1 = arrayFromListN (sz_underlying - 1)
  [ arr
  | (ix, el) <- itoListFromTill 0 (sz_underlying - 1)  els
  , let !arr =  arrayFromListN (sz_underlying - ix - 1)
                [set | ar <- toListFrom (ix + 1) c1, let right = ar `A.indexArray` 0, let !set = Bin 2 el S.empty right]
  ]
  where
    !sz_underlying = A.sizeofArray els


combine3
  :: Int  -- The size of the left subtrees
  -> Array (Array (Set a)) -- A column of potential left subtrees. The outer
                           -- array indexed by starting element.
  -> Array (PrimArray Word8)  -- Maximal indices of corresponding left sets.
  -> Array a -- Elements to choose as roots
  -> Int  -- size of right subsets
  -> Array (Array (Set a)) -- Potential right subtrees
  -> [Set a]
combine3 sz_left all_lefts all_ix_left_maxes els sz_right rights = concat
  [ combineTwo sz_left lefts ix_left_maxes els sz_right rights
  | (lix, lefts) <- itoListFromTill 0 (A.sizeofArray els - sz_left - sz_right) all_lefts
  , let !ix_left_maxes = all_ix_left_maxes `A.indexArray` lix
  ]

combine3A
  :: Pascal
  -> Int  -- The size of the left subtrees
  -> Array (Array (Set a)) -- A column of potential left subtrees. The outer
                           -- array indexed by starting element.
  -> Array (PrimArray Word8)  -- Maximal indices of corresponding left sets.
  -> Array a -- Elements to choose as roots
  -> Int  -- size of right subsets
  -> Array (Array (Set a)) -- Potential right subtrees
  -> Array (Array (Set a))
combine3A pascal sz_left all_lefts all_ix_left_maxes els sz_right rights =
  A.arrayFromList -- TODO: calculate the length up front. Low priority.
  [ arrayFromListN (arrSize pascal sz_underlying (sz_left + sz_right + 1) lix) $ combineTwo sz_left lefts ix_left_maxes els sz_right rights
  | (lix, lefts) <- itoListFromTill 0 (A.sizeofArray els - sz_left - sz_right) all_lefts
  , let !ix_left_maxes = all_ix_left_maxes `A.indexArray` lix
  ]
  where
    sz_underlying = A.sizeofArray els

arrayFromList' :: [a] -> Array a
arrayFromList' xs = A.arrayFromList [x | !x <- xs]


combineTwo
  :: Int  -- The size of the left subtrees
  -> Array (Set a) -- Potential left subtrees, all with the same minimal
                   -- element
  -> PrimArray Word8 -- Maximal indices of the potential left subtrees
  -> Array a -- Elements to choose as roots
  -> Int     -- The size of the right subsets
  -> Array (Array (Set a)) -- The subsets to (potentially) choose as right subtrees.
                           -- The outer array is indexed by starting value, and the
                           -- inner one is just a list in order.
  -> [Set a]
combineTwo sz_left lefts ix_left_maxes els sz_right rights
  = [ subset
    | (ix_left, left) <- itoListFrom 0 lefts
    , let !ix_left_max = fromIntegral $ ix_left_maxes `PA.indexPrimArray` ix_left
    , ix_left_max + sz_right < A.sizeofArray els
    , !subset <- combineOne sz_left left ix_left_max els sz_right rights
    ]
{-# INLINE combineTwo #-}


combineOne
  :: Int       -- The size of the left subtrees
  -> Set a     -- The left subtree
  -> Int       -- The index of the maximum element of the left subtree
  -> Array a   -- The elements (to choose as roots)
  -> Int       -- The size of the right subsets
  -> Array (Array (Set a)) -- The subsets to (potentially) choose as right subtrees.
                           -- The outer array is indexed by starting value, and the
                           -- inner one is just a list in order.
  -> [Set a]
combineOne sz_left left ix_left_max els sz_right rights
  = [ set
    | (root_ix, root) <- itoListFromTill (ix_left_max + 1) (A.sizeofArray els - sz_right) els
    , ra <- toListFrom (root_ix + 1) rights
    , right <- F.toList ra
      -- We use Bin instead of bin to avoid having to inspect the subtrees. Thanks to
      -- pointer tagging, we should be able to verify that the subtrees are in WHNF
      -- without dereferencing the pointers to them.
    , let !set = Bin (sz_left + sz_right + 1) root left right
    ]
-- We inline this so it can fuse into combineTwo, avoiding contatenation and
-- (I imagine) also avoiding intermediate lists when we're creating arrays.
{-# INLINE combineOne #-}


-- Note: Word8
--
-- On a 64-bit machine, our Set representation can only dream of representing a
-- set of up to 2^63-1 elements, so we can only dream of taking the power set
-- of a set with up to 62 elements (and I don't know if any extant computer can
-- even do that). So on such a machine, we clearly only need 6 bits to
-- represent indices into the underlying set. One might wonder, however,
-- whether some future machine with a word size of over 256 bits and and
-- absurdly large memory might need more than 8 bits. The answer is no: 2^256
-- bits is greater than the information capacity of the entire observable
-- universe. So 8 bits really are all anyone will ever need.

foldrFrom :: (a -> b -> b) -> b -> Int -> Array a -> b
foldrFrom f = \z !start !ary ->
  let
    !sz = A.sizeofArray ary
    go i
      | i == sz = z
      | (# x #) <- indexArray## ary i
      = f x (go (i + 1))
    in go start
{-# INLINE foldrFrom #-}

ifoldrFrom :: (Int -> a -> b -> b) -> b -> Int -> Array a -> b
ifoldrFrom f = \z !start !ary ->
  let
    !sz = A.sizeofArray ary
    go i
      | i == sz = z
      | (# x #) <- indexArray## ary i
      = f i x (go (i + 1))
    in go start
{-# INLINE ifoldrFrom #-}

-- Convert a portion of an array to a list, starting with the given index.
toListFrom :: Int -> Array a -> [a]
toListFrom !start !ary = E.build $ \c n -> foldrFrom c n start ary
{-# INLINE toListFrom #-}

itoListFrom :: Int -> Array a -> [(Int, a)]
itoListFrom !start !ary = E.build $ \c n -> ifoldrFrom (\i a r -> (i, a) `c` r) n start ary
{-# INLINE itoListFrom #-}

itoListFromTill :: Int -> Int -> Array a -> [(Int, a)]
itoListFromTill !start !end !ary = E.build $ \c n -> ifoldrFromTill (\i a r -> (i, a) `c` r) n start end ary
{-# INLINE itoListFromTill #-}

foldrFromTill :: (a -> b -> b) -> b -> Int -> Int -> Array a -> b
foldrFromTill f = \z !start !end !ary ->
  let
--    !sz = A.sizeofArray ary
    go i
      | i == end = z
      | (# x #) <- indexArray## ary i
      = f x (go (i + 1))
    in go start
{-# INLINE foldrFromTill #-}

ifoldrFromTill :: (Int -> a -> b -> b) -> b -> Int -> Int -> Array a -> b
ifoldrFromTill f = \z !start !end !ary ->
  let
--    !sz = A.sizeofArray ary
    go i
      | i == end = z
      | (# x #) <- indexArray## ary i
      = f i x (go (i + 1))
    in go start
{-# INLINE ifoldrFromTill #-}

-- Convert a portion of an array to a list. starting with the given start index
-- and ending one short of the given end index.
toListFromTill :: Int -> Int -> Array a -> [a]
toListFromTill !start !end !ary = E.build $ \c n -> foldrFromTill c n start end ary
{-# INLINE toListFromTill #-}

-- | Convert an array to a list eagerly. That is, we create the entire list,
-- rather than just creating the first cons and waiting for more to be
-- demanded. This is helpful when the elements are large objects (in our case
-- they're arrays themselves), because they will be released as they are
-- processed rather than being kept alive by the original array.
--
-- @
-- arrayToListEager ary = length lst `seq` lst
--   where
--     lst = arrayToList ary
-- @
arrayToListEager :: A.Array a -> [a]
arrayToListEager !ary = go 0
  where
    sz = A.sizeofArray ary
    go i
      | i == sz = []
      | (# x #) <- indexArray## ary i
      = (x :) $! go (i + 1)


{-
Suppose we are producing sets of size s, starting with i0. Suppose the left
sets have size sl and the right sets have size sr (as usual, |sr - sl| <= 1,
and I think for now I'll assume that sl <= sr).
-}

-- Pascal's triangle up to some size. For now, we don't take advantage of its
-- symmetry, or of the boringly repetitive edges.
newtype Pascal = Pascal (Array (PrimArray Int))
  deriving Show

-- Generate enough of Pascal's triangle to calculate combinations up to @n@.
mkPascal :: Int -> Pascal
-- This isn't super-optimized, but it should be plenty good enough for our purposes.
-- We don't use the classic Haskell infinite-list construction because GHC would
-- float the list out, leaking (a little) memory.
mkPascal n = Pascal . arrayFromListN (n + 1) $ primArrayFromListN 1 [1] : triangle 0 (primArrayFromListN 1 [1])
  where
    triangle k _
      | k == n = []
    triangle k row = nr : triangle (k + 1) nr
      where
        nr = primArrayFromListN (k + 2) (zipWith (+) (0 : PA.primArrayToList row) (PA.primArrayToList row ++ [0]))

-- Given at least @n@ rows of Pascal's triangle, calculate
comb :: Pascal -> Int -> Int -> Int
comb (Pascal ary) n r
  | n < 0 || r < 0
  = error "Negative combination"
  | n >= A.sizeofArray ary
  = error "Combination out of Pascal range"
  | r > n = 0
  | otherwise = (ary `A.indexArray` (n - 0)) `PA.indexPrimArray` (r - 0)

-- | Given an underlying set of size @set_size@,
-- @arrSize pasc set_size subset_size first_ix@ is the number of subsets of
-- size @subset_size@ whose minimal index is @first_ix@.
arrSize :: Pascal -> Int -> Int -> Int -> Int
arrSize pasc set_size subset_size first_ix
  = comb pasc (set_size - first_ix - 1) (subset_size - 1)

imap :: (Int -> a -> b) -> [a] -> [b]
imap f xs = E.build $ \ c n ->
  foldr (\a r !i -> f i a `c` r (i + 1)) (\ !_i -> n) xs 0
{-# INLINE imap #-}

-- Unlike the version in the primitive package, this one is a good consumer
-- for list fusion.
arrayFromListN :: {- HasCallStack => -} Int -> [a] -> Array a
arrayFromListN n l =
  A.createArray n (die "fromListN: uninitialized element") $ \sma ->
      let
        go x r !ix
          | ix < n
          = do
              A.writeArray sma ix x
              r (ix+1)
          | otherwise = die "fromListN: list length greater than specified size"
        stop !ix
          | ix == n
          = pure ()
          | otherwise = die "fromListN: list length less than specified size"
      in foldr go stop l 0
{-# INLINE arrayFromListN #-}

-- No stack trace
die :: {- HasCallStack => -} String -> a
die = error


primArrayFromListN :: forall a. Prim a => Int -> [a] -> PrimArray a
primArrayFromListN len vs = runST run where
  run :: forall s. ST s (PrimArray a)
  run = do
    arr <- PA.newPrimArray len
    let
      go :: a -> (Int -> ST s ()) -> Int -> ST s ()
      go a r !ix
        | ix < len
        = do
            PA.writePrimArray arr ix a
            r (ix + 1)
        | otherwise
        = die "fromListN: list length greater than specified size"
      stop :: Int -> ST s ()
      stop ix
        | ix == len
        = pure ()
        | otherwise
        = die "fromListN: list length less than specified size"
    foldr go stop vs 0
    PA.unsafeFreezePrimArray arr

{-

-- | Strict map over the elements of the array.
imapArray' :: (Int -> a -> b) -> Array a -> Array b
imapArray' f a =
  A.createArray (A.sizeofArray a) (error "possible imp") $ \mb ->
    let go i | i == A.sizeofArray a
             = pure ()
             | otherwise
             = do x <- A.indexArrayM a i
                  -- We use indexArrayM here so that we will perform the
                  -- indexing eagerly even if f is lazy.
                  let !y = f i x
                  A.writeArray mb i y >> go (i + 1)
     in go 0
{-# INLINE imapArray' #-}
-}
