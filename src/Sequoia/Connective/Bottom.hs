module Sequoia.Connective.Bottom
( -- * Negative falsity
  Bottom(..)
) where

import Sequoia.Polarity

-- Negative falsity

newtype Bottom r = Bottom { absurdN :: r }

instance Polarized N (Bottom r) where
