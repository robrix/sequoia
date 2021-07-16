module Sequoia.Profunctor.Diagonal
( Diagonal(..)
, Codiagonal(..)
) where

import Control.Monad (join)
import Data.Profunctor

class Profunctor p => Diagonal p where
  dup :: a `p` (a, a)

instance Diagonal (->) where
  dup = join (,)


class Profunctor p => Codiagonal p where
  dedup :: Either a a `p` a
