module Sequoia.Connective.Bottom
( -- * Negative falsity
  Bottom
, absurdN
) where

import Sequoia.Polarity

-- Negative falsity

data Bottom r

instance Polarized N (Bottom r) where

absurdN :: Bottom r -> a
absurdN = \case
