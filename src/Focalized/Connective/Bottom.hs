module Focalized.Connective.Bottom
( -- * Negative falsity
  Bottom
, absurdN
) where

import Focalized.Polarity

-- Negative falsity

data Bottom

instance Polarized N Bottom where

absurdN :: Bottom -> a
absurdN = \case
