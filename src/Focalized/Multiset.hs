module Focalized.Multiset
( Multiset
, singleton
) where

import qualified Data.Map as M

newtype Multiset a = Multiset (M.Map a Word)
  deriving (Eq, Ord)

singleton :: a -> Multiset a
singleton a = Multiset (M.singleton a 1)
