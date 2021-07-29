module Sequoia.Connective.One
( -- * Positive truth
  One(..)
) where

import Sequoia.Polarity

-- Positive truth

data One e = One
  deriving (Eq, Ord, Show)

instance Polarized P (One e) where
