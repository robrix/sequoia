module Focalized.Multiset
( Multiset
, singleton
, empty
, fromList
, insert
, delete
, multiplicity
, cardinality
, elems
, distinctElems
, quotients
) where

import           Data.Foldable (foldl')
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (stimes)

newtype Multiset a = Multiset (M.Map a Word)
  deriving (Eq, Ord)

instance Show a => Show (Multiset a) where
  showsPrec _ (Multiset m) = showList (M.toList m)

instance Ord a => Semigroup (Multiset a) where
  Multiset a <> Multiset b = Multiset (M.unionWith (+) a b)

instance Ord a => Monoid (Multiset a) where
  mempty = empty

instance Foldable Multiset where
  foldMap f (Multiset m) = M.foldMapWithKey (\ a n -> stimes n (f a)) m
  length = fromIntegral . cardinality

singleton :: a -> Multiset a
singleton a = Multiset (M.singleton a 1)

empty :: Multiset a
empty = Multiset M.empty

fromList :: Ord a => [a] -> Multiset a
fromList = foldl' (flip insert) empty


insert :: Ord a => a -> Multiset a -> Multiset a
insert a (Multiset as) = Multiset (M.insertWith (+) a 1 as)

delete :: Ord a => a -> Multiset a -> Multiset a
delete a (Multiset as) = Multiset (M.update decr a as)
  where
  decr i
    | i <= 1    = Nothing
    | otherwise = Just (i - 1)


multiplicity :: Ord a => a -> Multiset a -> Word
multiplicity a (Multiset as) = fromMaybe 0 (M.lookup a as)

cardinality :: Multiset a -> Word
cardinality (Multiset as) = sum as


elems :: Multiset a -> [a]
elems (Multiset m) = [a' | (a, n) <- M.toList m, a' <- stimes n [a] ]

distinctElems :: Multiset a -> [a]
distinctElems (Multiset m) = M.keys m


quotients :: Ord a => Multiset a -> [(a, Multiset a)]
quotients m = [ (a, delete a m) | a <- distinctElems m ]
