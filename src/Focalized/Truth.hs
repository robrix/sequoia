module Focalized.Truth
( -- * Negative truth
  Top(..)
  -- * Positive truth
, One(..)
) where

import Focalized.Polarity

-- Negative truth

data Top = Top
  deriving (Eq, Ord, Show)

instance Polarized N Top where


-- Positive truth

data One = One
  deriving (Eq, Ord, Show)

instance Polarized P One where
