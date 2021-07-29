module Sequoia.Connective.One
( -- * Positive truth
  One(..)
) where

import Sequoia.Polarity

-- Positive truth

newtype One e = One { getOne :: e }
  deriving (Eq, Ord, Show)

instance Polarized P (One e) where
