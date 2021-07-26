{-# LANGUAGE TypeFamilies #-}
module Sequoia.List
( -- * Efficiently concatenable lists
  List(..)
  -- * Construction
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
) where

import Data.Foldable (Foldable(..))
import Data.Functor.Classes
import GHC.Exts (IsList(..))
import Prelude hiding (drop, dropWhile, filter, take, takeWhile)

-- Efficiently concatenable lists

newtype List a = List { foldList :: forall r . (a -> r -> r) -> r -> r }

instance Show1 List where
  liftShowsPrec _ showList _ = showList . runList

instance Show a => Show (List a) where
  showsPrec = showsPrec1

instance Semigroup (List a) where
  List a <> List b = List (\ cons -> a cons . b cons)

instance Monoid (List a) where
  mempty = nil

instance Functor List where
  fmap f (List l) = List (l . (. f))

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

nil :: List a
nil = List (const id)

cons :: a -> List a -> List a
cons h (List t) = List (\ cons -> cons h . t cons)

list :: [a] -> List a
list as = List (\ cons nil -> foldr cons nil as)


-- Elimination

runList :: List a -> [a]
runList (List l) = l (:) []


-- Computation

take :: Int -> List a -> List a
take n (List l) = List (\ cons nil -> l (\ h t n -> if n <= 0 then nil else cons h (t (n - 1))) (const nil) n)

drop :: Int -> List a -> List a
drop n l = List (\ cons nil -> foldList l (\ h t n -> if n <= 0 then cons h (t n) else t (n - 1)) (const nil) n)

takeWhile :: (a -> Bool) -> (List a -> List a)
takeWhile p l = List (\ cons nil -> foldList l (\ h t -> if p h then cons h t else nil) nil)

dropWhile :: (a -> Bool) -> (List a -> List a)
dropWhile p l = List (\ cons nil -> foldList l (\ h t done -> if done then cons h (t done) else if p h then t done else cons h (t True)) (const nil) False)

filter :: (a -> Bool) -> (List a -> List a)
filter p l = List (\ cons -> foldList l (\ h t -> if p h then cons h t else t))
