module Focalized.Multiset
( Multiset
, singleton
, empty
, insert
, delete
) where

import qualified Data.Map as M

newtype Multiset a = Multiset (M.Map a Word)
  deriving (Eq, Ord)

instance Show a => Show (Multiset a) where
  showsPrec _ (Multiset m) = showList (M.toList m)

instance Ord a => Semigroup (Multiset a) where
  Multiset a <> Multiset b = Multiset (M.unionWith (+) a b)

instance Ord a => Monoid (Multiset a) where
  mempty = empty

singleton :: a -> Multiset a
singleton a = Multiset (M.singleton a 1)

empty :: Multiset a
empty = Multiset M.empty


insert :: Ord a => a -> Multiset a -> Multiset a
insert a (Multiset as) = Multiset (M.insertWith (+) a 1 as)

delete :: Ord a => a -> Multiset a -> Multiset a
delete a (Multiset as) = Multiset (M.update decr a as)
  where
  decr i
    | i <= 0    = Nothing
    | otherwise = Just (i - 1)
