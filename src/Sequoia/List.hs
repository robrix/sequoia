{-# LANGUAGE TypeFamilies #-}
module Sequoia.List
( -- * Efficiently concatenable lists
  List(..)
  -- * Construction
, fromList
  -- * Elimination
, runList
) where

import Data.Foldable (Foldable(..))
import GHC.Exts (IsList(..))

-- Efficiently concatenable lists

newtype List a = List (forall r . (a -> r -> r) -> r -> r)

instance Semigroup (List a) where
  List a <> List b = List (\ cons -> a cons . b cons)

instance Monoid (List a) where
  mempty = List (const id)

instance Foldable List where
  foldMap f = foldMap f . runList
  toList = runList

instance IsList (List a) where
  type Item (List a) = a
  fromList as = List (\ cons nil -> foldr cons nil as)
  toList = runList


-- Elimination

runList :: List a -> [a]
runList (List l) = l (:) []
