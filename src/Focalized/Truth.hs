module Focalized.Truth
( -- * Negative truth
  Top(..)
  -- * Positive truth
, One(..)
) where

import Focalized.Polarity

data Top = Top
  deriving (Eq, Ord, Show)

instance Polarized N Top where


data One = One
  deriving (Eq, Ord, Show)

instance Polarized P One where
