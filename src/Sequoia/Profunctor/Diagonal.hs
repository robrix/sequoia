module Sequoia.Profunctor.Diagonal
( Diagonal(..)
) where

import Data.Profunctor

class Profunctor p => Diagonal p where
  dup :: a `p` (a, a)
