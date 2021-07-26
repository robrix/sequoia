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
, list
  -- * Elimination
, runList
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
) where

import Data.Foldable (Foldable(..))
import Data.Functor.Classes
import GHC.Exts (IsList(..))
import Prelude hiding (drop, dropWhile, filter, take, takeWhile, zip, zipWith)

-- Efficiently concatenable lists

type Foldl r a = (r -> a -> r) -> r -> r
type Foldr r a = (a -> r -> r) -> r -> r
type FoldMap m a = (m -> m -> m) -> (a -> m) -> m -> m

newtype List a = List { foldList :: forall r . Foldr r a }

instance Show1 List where
  liftShowsPrec _ showList _ = showList . runList

instance Show a => Show (List a) where
  showsPrec = showsPrec1

instance Semigroup (List a) where
  a <> b = fromFoldr (\ cons -> foldList a cons . foldList b cons)

instance Monoid (List a) where
  mempty = nil

instance Functor List where
  fmap f l = fromFoldr (foldList l . (. f))

instance Foldable List where
  foldr cons nil list = foldList list cons nil
  foldMap f list = foldList list ((<>) . f) mempty
  toList = runList
  null list = foldList list (const (const False)) True

instance IsList (List a) where
  type Item (List a) = a
  fromList = list
  toList = runList


-- Construction

fromFoldr :: (forall r . Foldr r a) -> List a
fromFoldr = List

nil :: List a
nil = fromFoldr (const id)

cons :: a -> List a -> List a
cons h t = fromFoldr (\ cons -> cons h . foldList t cons)

list :: [a] -> List a
list as = fromFoldr (\ cons nil -> foldr cons nil as)


-- Elimination

runList :: List a -> [a]
runList l = foldList l (:) []


-- Computation

take :: Int -> List a -> List a
take n l = fromFoldr (\ cons nil -> foldList l (\ h t n -> if n <= 0 then nil else cons h (t (n - 1))) (const nil) n)

drop :: Int -> List a -> List a
drop n l = fromFoldr (\ cons nil -> foldList l (\ h t n -> if n <= 0 then cons h (t n) else t (n - 1)) (const nil) n)

takeWhile :: (a -> Bool) -> (List a -> List a)
takeWhile p l = fromFoldr (\ cons nil -> foldList l (\ h t -> if p h then cons h t else nil) nil)

dropWhile :: (a -> Bool) -> (List a -> List a)
dropWhile p l = fromFoldr (\ cons nil -> foldList l (\ h t done -> if done then cons h (t done) else if p h then t done else cons h (t True)) (const nil) False)

filter :: (a -> Bool) -> (List a -> List a)
filter p l = fromFoldr (\ cons -> foldList l (\ h t -> if p h then cons h t else t))

zip :: List a -> List b -> List (a, b)
zip = zipWith (,)

zipWith :: (a -> b -> c) -> (List a -> List b -> List c)
zipWith f a b = fromFoldr (\ cons nil -> foldList a (\ ha t b -> foldList b (\ hb _ -> cons (f ha hb) (t (drop 1 b))) nil) (const nil) b)


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
