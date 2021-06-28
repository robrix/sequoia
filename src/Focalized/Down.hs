module Focalized.Down
( -- * Negative-to-positive shift
  Down(..)
) where

import Data.Functor.Identity
import Focalized.Polarity

-- Negative-to-positive shift

newtype Down a = Down { getDown :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Neg a => Polarized P (Down a) where
