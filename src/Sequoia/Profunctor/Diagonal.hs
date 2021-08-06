module Sequoia.Profunctor.Diagonal
( -- * Diagonal functors
  Diagonal(..)
  -- * Codiagonal functors
, Codiagonal(..)
, swap
, mirror
  -- * Defaults
, dupArrow
, dedupArrow
  -- * Diagonal functor
, Δ(..)
) where

import Control.Arrow (Arrow(..), Kleisli(..))
import Control.Comonad
import Data.Profunctor
import Data.Profunctor.Strong
import Data.Tuple (swap)

-- Diagonal functors

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

instance Arrow p => Diagonal (WrappedArrow p) where
  dup = WrapArrow (arr dup)


-- Codiagonal functors

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

instance Arrow p => Codiagonal (WrappedArrow p) where
  dedup = WrapArrow (arr dedup)


mirror :: Either a b -> Either b a
mirror = either Right Left


-- Defaults

dupArrow :: Arrow p => a `p` (a, a)
dupArrow = arr dup

dedupArrow :: Arrow p => Either a a `p` a
dedupArrow = arr dedup


-- Diagonal functor

newtype Δ a = Δ { exDiag :: (a, a) }
  deriving (Functor)
