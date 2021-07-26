{-# LANGUAGE TypeFamilies #-}
module Sequoia.List
( -- * Efficiently concatenable lists
  List(..)
  -- * Construction
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

newtype List a = List (forall r . (a -> r -> r) -> r -> r)

instance Show1 List where
  liftShowsPrec _ showList _ = showList . runList

instance Show a => Show (List a) where
  showsPrec = showsPrec1

instance Semigroup (List a) where
  List a <> List b = List (\ cons -> a cons . b cons)

instance Monoid (List a) where
  mempty = List (const id)

instance Foldable List where
  foldMap f = foldMap f . runList
  toList = runList

instance IsList (List a) where
  type Item (List a) = a
  fromList = list
  toList = runList


-- Construction

list :: [a] -> List a
list as = List (\ cons nil -> foldr cons nil as)


-- Elimination

runList :: List a -> [a]
runList (List l) = l (:) []


-- Computation

take :: Int -> List a -> List a
take n (List l) = List (\ cons nil -> l (\ h t n -> if n <= 0 then nil else cons h (t (n - 1))) (const nil) n)
