module Sequoia.Profunctor.Diagonal
( Diagonal(..)
, Codiagonal(..)
, swap
) where

import Control.Arrow (Kleisli(..))
import Control.Comonad
import Data.Profunctor
import Data.Profunctor.Strong
import Data.Tuple (swap)

class Profunctor p => Diagonal p where
  dup :: a `p` (a, a)

instance Diagonal (->) where
  dup a = (a, a)

instance Monad m => Diagonal (Kleisli m) where
  dup = Kleisli (pure . dup)

instance Diagonal p => Diagonal (Pastro p) where
  dup = Pastro fst dup (,())

instance Diagonal p => Diagonal (Copastro p) where
  dup = Copastro ($ dup)

instance Applicative f => Diagonal (Star f) where
  dup = Star (pure . dup)

instance Comonad f => Diagonal (Costar f) where
  dup = Costar (dup . extract)


class Profunctor p => Codiagonal p where
  dedup :: Either a a `p` a

instance Codiagonal (->) where
  dedup = either id id

instance Monad m => Codiagonal (Kleisli m) where
  dedup = Kleisli (pure . dedup)

instance Codiagonal p => Codiagonal (Pastro p) where
  dedup = Pastro fst dedup (,())

instance Codiagonal p => Codiagonal (Copastro p) where
  dedup = Copastro ($ dedup)

instance Applicative f => Codiagonal (Star f) where
  dedup = Star (pure . dedup)

instance Comonad f => Codiagonal (Costar f) where
  dedup = Costar (dedup . extract)
