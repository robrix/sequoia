{-# LANGUAGE TypeFamilies #-}
module Sequoia.List
( -- * Efficiently concatenable lists
  Foldl
, Foldr
, FoldMap
, List(..)
  -- * Construction
, fromFoldr
, nil
, cons
, Sequoia.List.fromList
  -- * Elimination
, Sequoia.List.toList
, head
, tail
, uncons
  -- * Computation
, take
, drop
, takeWhile
, dropWhile
, filter
, zip
, zipWith
, These(..)
, these
, align
, alignWith
) where

import Control.Applicative (liftA2)
import Data.Bool (bool)
import Data.Foldable (Foldable(..))
import Data.Functor.Classes
import GHC.Exts (IsList(..))
import Prelude hiding (drop, dropWhile, filter, head, tail, take, takeWhile, zip, zipWith)

-- Efficiently concatenable lists

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
  liftShowsPrec _ showList _ = showList . Sequoia.List.toList

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
  toList = Sequoia.List.toList
  null list = toFoldr list (const (const False)) True

instance Traversable List where
  traverse f = foldr (liftA2 cons . f) (pure nil)

instance IsList (List a) where
  type Item (List a) = a
  fromList = Sequoia.List.fromList
  toList = Sequoia.List.toList


-- Construction

fromFoldr :: (forall r . Foldr r a) -> List a
fromFoldr = FromFoldr

nil :: List a
nil = fromFoldr (const id)

cons :: a -> List a -> List a
cons h t = fromFoldr (\ cons -> cons h . toFoldr t cons)

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

zip :: List a -> List b -> List (a, b)
zip = zipWith (,)

zipWith :: (a -> b -> c) -> (List a -> List b -> List c)
zipWith f a b = fromFoldr (\ cons nil -> toFoldr a (\ ha t b -> toFoldr b (\ hb _ -> cons (f ha hb) (t (tail b))) nil) (const nil) b)


data These a b
  = This a
  | That b
  | These a b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

these :: (a -> r) -> (b -> r) -> (a -> b -> r) -> (These a b -> r)
these f g h = \case
  This a    -> f a
  That b    -> g b
  These a b -> h a b

align :: List a -> List b -> List (These a b)
align = alignWith id

alignWith :: (These a b -> c) -> (List a -> List b -> List c)
alignWith f as bs = fromFoldr
  (\ cons nil -> foldr
    (\ a recur bs -> foldr
      (\ b _ -> cons (f (These a b)) (recur (tail bs)))
      (cons (f (This a)) (recur bs))
      bs)
  (foldr (cons . f . That) nil)
  as bs)
