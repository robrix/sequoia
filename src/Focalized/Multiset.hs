module Focalized.Multiset
( Multiset
, singleton
, empty
) where

import qualified Data.Map as M

newtype Multiset a = Multiset (M.Map a Word)
  deriving (Eq, Ord)

instance Show a => Show (Multiset a) where
  showsPrec _ (Multiset m) = showList (M.toList m)

instance Ord a => Semigroup (Multiset a) where
  Multiset a <> Multiset b = Multiset (M.unionWith (+) a b)

singleton :: a -> Multiset a
singleton a = Multiset (M.singleton a 1)

empty :: Multiset a
empty = Multiset M.empty
