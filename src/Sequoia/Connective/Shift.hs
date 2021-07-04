module Sequoia.Connective.Shift
( -- * Up
  Up(..)
  -- * Down
, Down(..)
) where

import Sequoia.Functor.I
import Sequoia.Polarity

-- Up

newtype Up a = Up { getUp :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via I

instance Pos a => Polarized N (Up a) where


-- Down

newtype Down a = Down { getDown :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via I

instance Neg a => Polarized P (Down a) where
