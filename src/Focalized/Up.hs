module Focalized.Up
( -- * Positive-to-negative shift
  Up(..)
) where

import Data.Functor.Identity
import Focalized.Polarity

-- Positive-to-negative shift

newtype Up   a = Up   { getUp   :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Pos a => Polarized N (Up a) where
