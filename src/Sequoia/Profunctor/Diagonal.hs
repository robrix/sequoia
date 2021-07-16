module Sequoia.Profunctor.Diagonal
( Diagonal(..)
, Codiagonal(..)
) where

import Control.Arrow (Kleisli(..))
import Data.Profunctor
import Data.Profunctor.Strong

class Profunctor p => Diagonal p where
  dup :: a `p` (a, a)

instance Diagonal (->) where
  dup a = (a, a)

instance Monad m => Diagonal (Kleisli m) where
  dup = Kleisli (pure . dup)

instance Diagonal p => Diagonal (Pastro p) where
  dup = Pastro fst dup (,())


class Profunctor p => Codiagonal p where
  dedup :: Either a a `p` a

instance Codiagonal (->) where
  dedup = either id id

instance Monad m => Codiagonal (Kleisli m) where
  dedup = Kleisli (pure . dedup)

instance Codiagonal p => Codiagonal (Pastro p) where
  dedup = Pastro fst dedup (,())
