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
) where

import Data.Foldable (Foldable(..))
import Data.Functor.Classes
import GHC.Exts (IsList(..))
import Prelude hiding (take)

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
