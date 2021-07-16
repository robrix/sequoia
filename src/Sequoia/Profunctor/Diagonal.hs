module Sequoia.Profunctor.Diagonal
( Diagonal(..)
, Codiagonal(..)
) where

import Control.Arrow (Kleisli(..))
import Data.Profunctor

class Profunctor p => Diagonal p where
  dup :: a `p` (a, a)

instance Diagonal (->) where
  dup a = (a, a)

instance Monad m => Diagonal (Kleisli m) where
  dup = Kleisli (pure . dup)


class Profunctor p => Codiagonal p where
  dedup :: Either a a `p` a

instance Codiagonal (->) where
  dedup = either id id

instance Monad m => Codiagonal (Kleisli m) where
  dedup = Kleisli (pure . dedup)
