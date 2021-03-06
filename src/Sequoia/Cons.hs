{-# LANGUAGE TypeFamilies #-}
module Sequoia.Cons
( -- * Efficiently concatenable cons lists
  Foldl
, Foldr
, FoldMap
, List(..)
  -- * Construction
, fromFoldr
, nil
, cons
, snoc
, singleton
, Sequoia.Cons.fromList
  -- * Elimination
, Sequoia.Cons.toList
, head
, tail
, uncons
  -- * Computation
, take
, drop
, takeWhile
, dropWhile
, filter
, reverse
, repeat
, zip
, zipWith
, These(..)
, these
, align
, alignWith
) where

import Control.Applicative (Alternative(..), liftA2)
import Control.Monad.Zip
import Data.Bifunctor (Bifunctor(..))
import Data.Bool (bool)
import Data.Foldable (Foldable(..))
import Data.Functor.Classes
import Data.Semialign (Align(..), Repeat(..), Semialign(..), Unalign(..), Unzip(..), Zip(..))
import Data.These
import GHC.Exts (IsList(..))
import Prelude hiding (drop, dropWhile, filter, head, repeat, reverse, tail, take, takeWhile, zip, zipWith)

-- Efficiently concatenable cons lists

type Foldl r a = (r -> a -> r) -> r -> r
type Foldr r a = (a -> r -> r) -> r -> r
type FoldMap m a = (m -> m -> m) -> (a -> m) -> m -> m

newtype List a = FromFoldr { toFoldr :: forall r . Foldr r a }

instance Eq1 List where
  liftEq (==) as bs = foldr (\ a isEq bs -> foldr (\ b _ -> a == b && isEq (tail bs)) False bs) null as bs

instance Eq a => Eq (List a) where
  (==) = eq1

instance Ord1 List where
  liftCompare compare as bs = foldr (\ a cmp bs -> foldr (\ b _ -> compare a b <> cmp (tail bs)) GT bs) (const LT) as bs

instance Ord a => Ord (List a) where
  compare = compare1

instance Show1 List where
  liftShowsPrec _ showList _ = showList . Sequoia.Cons.toList

instance Show a => Show (List a) where
  showsPrec = showsPrec1

instance Semigroup (List a) where
  a <> b = fromFoldr (\ cons -> toFoldr a cons . toFoldr b cons)

instance Monoid (List a) where
  mempty = nil

instance Functor List where
  fmap f l = fromFoldr (toFoldr l . (. f))

instance Foldable List where
  foldr cons nil list = toFoldr list cons nil
  foldMap f list = toFoldr list ((<>) . f) mempty
  toList = Sequoia.Cons.toList
  null list = toFoldr list (const (const False)) True

instance Traversable List where
  traverse f = foldr (liftA2 cons . f) (pure nil)

instance Applicative List where
  pure = singleton
  liftA2 f a b = foldr (\ a cs -> foldr (cons . f a) cs b) nil a
  f <*> a = foldr (\ f bs -> foldr (cons . f) bs a) nil f

instance Alternative List where
  empty = nil
  (<|>) = (<>)

instance Monad List where
  l >>= f = foldr ((<>) . f) nil l

instance MonadZip List where
  mzip = zip
  mzipWith = zipWith

instance Semialign List where
  align = alignWith id

  alignWith f as bs = fromFoldr
    (\ cons nil -> foldr
      (\ a recur bs -> foldr
        (\ b _ -> cons (f (These a b)) (recur (tail bs)))
        (cons (f (This a)) (recur bs))
        bs)
    (foldr (cons . f . That) nil)
    as bs)

instance Align List where
  nil = fromFoldr (const id)

instance Unalign List where
  unalign = foldr (these (first . cons) (second . cons) ((. cons) . bimap . cons)) (nil, nil)

instance Zip List where
  zip = zipWith (,)

  zipWith f a b = fromFoldr (\ cons nil -> toFoldr a (\ ha t b -> toFoldr b (\ hb _ -> cons (f ha hb) (t (tail b))) nil) (const nil) b)

instance Unzip List where
  unzip       = (,) <$> fmap  fst      <*> fmap  snd
  unzipWith f = (,) <$> fmap (fst . f) <*> fmap (snd . f)

instance Repeat List where
  repeat a = cons a (repeat a)

instance IsList (List a) where
  type Item (List a) = a
  fromList = Sequoia.Cons.fromList
  toList = Sequoia.Cons.toList


-- Construction

fromFoldr :: (forall r . Foldr r a) -> List a
fromFoldr = FromFoldr

cons :: a -> List a -> List a
cons h t = fromFoldr (\ cons -> cons h . toFoldr t cons)

snoc :: List a -> a -> List a
snoc i l = fromFoldr (\ cons nil -> foldr cons (cons l nil) i)

singleton :: a -> List a
singleton a = cons a nil

fromList :: [a] -> List a
fromList as = fromFoldr (\ cons nil -> foldr cons nil as)


-- Elimination

toList :: List a -> [a]
toList = foldr (:) []

head :: List a -> Maybe a
head = foldr (const . Just) Nothing

tail :: List a -> List a
tail l = foldr (\ h t -> bool (cons h (t False)) (t False)) (const nil) l True

uncons :: List a -> Maybe (a, List a)
uncons = liftA2 (,) <$> head <*> Just . tail


-- Computation

take :: Int -> List a -> List a
take n l = fromFoldr (\ cons nil -> toFoldr l (\ h t n -> if n <= 0 then nil else cons h (t (n - 1))) (const nil) n)

drop :: Int -> List a -> List a
drop n l = fromFoldr (\ cons nil -> toFoldr l (\ h t n -> if n <= 0 then cons h (t n) else t (n - 1)) (const nil) n)

takeWhile :: (a -> Bool) -> (List a -> List a)
takeWhile p l = fromFoldr (\ cons nil -> toFoldr l (\ h t -> if p h then cons h t else nil) nil)

dropWhile :: (a -> Bool) -> (List a -> List a)
dropWhile p l = fromFoldr (\ cons nil -> toFoldr l (\ h t done -> if done then cons h (t done) else if p h then t done else cons h (t True)) (const nil) False)

filter :: (a -> Bool) -> (List a -> List a)
filter p l = fromFoldr (\ cons -> toFoldr l (\ h t -> if p h then cons h t else t))

reverse :: List a -> List a
reverse l = foldr (flip (.) . cons) id l nil
