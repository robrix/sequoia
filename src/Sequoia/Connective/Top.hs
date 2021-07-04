module Sequoia.Connective.Top
( -- * Negative truth
  Top(..)
) where

import Sequoia.Polarity

-- Negative truth

data Top = Top
  deriving (Eq, Ord, Show)

instance Polarized N Top where
