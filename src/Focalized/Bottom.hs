module Focalized.Bottom
( -- * Negative falsity
  Bot
, absurdN
) where

import Focalized.Polarity

-- Negative falsity

data Bot

instance Polarized N Bot where

absurdN :: Bot -> a
absurdN = \case
