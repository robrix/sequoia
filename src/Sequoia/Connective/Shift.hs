module Sequoia.Connective.Shift
( -- * Up
  Up(..)
  -- * Down
, Down(..)
) where

import Data.Functor.Identity
import Sequoia.Polarity

-- Up

newtype Up a = Up { getUp :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Pos a => Polarized N (Up a) where


-- Down

newtype Down a = Down { getDown :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Neg a => Polarized P (Down a) where
