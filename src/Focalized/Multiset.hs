module Focalized.Multiset
( Multiset
) where

import qualified Data.Map as M

newtype Multiset a = Multiset (M.Map a Word)
  deriving (Eq, Ord)
