{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Shift
( -- * Up
  Up(..)
  -- * Down
, Down(..)
) where

import Data.Distributive
import Data.Functor.Rep
import Sequoia.Functor.I
import Sequoia.Polarity

-- Up

newtype Up a = Up { getUp :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via I

instance Distributive Up where
  distribute = Up . fmap  getUp
  collect f  = Up . fmap (getUp . f)

instance Pos a => Polarized N (Up a) where


-- Down

newtype Down a = Down { getDown :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via I

instance Distributive Down where
  distribute = Down . fmap  getDown
  collect f  = Down . fmap (getDown . f)

instance Neg a => Polarized P (Down a) where
