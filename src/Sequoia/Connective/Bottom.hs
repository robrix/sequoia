module Sequoia.Connective.Bottom
( -- * Negative falsity
  Bottom(..)
) where

import Data.Functor.Identity
import Sequoia.Polarity

-- Negative falsity

newtype Bottom r = Bottom { absurdN :: r }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Polarized N (Bottom r) where
