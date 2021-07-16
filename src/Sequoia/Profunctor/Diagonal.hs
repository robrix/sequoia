module Sequoia.Profunctor.Diagonal
( Diagonal(..)
, Codiagonal(..)
) where

import Data.Profunctor

class Profunctor p => Diagonal p where
  dup :: a `p` (a, a)

instance Diagonal (->) where
  dup a = (a, a)


class Profunctor p => Codiagonal p where
  dedup :: Either a a `p` a

instance Codiagonal (->) where
  dedup = either id id
