module Focalized.Connective.Top
( -- * Negative truth
  Top(..)
) where

import Focalized.Polarity

-- Negative truth

data Top = Top
  deriving (Eq, Ord, Show)

instance Polarized N Top where
