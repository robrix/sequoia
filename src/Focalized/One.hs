module Focalized.One
( -- * Positive truth
  One(..)
) where

import Focalized.Polarity

-- Positive truth

data One = One
  deriving (Eq, Ord, Show)

instance Polarized P One where
