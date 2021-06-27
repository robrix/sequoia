module Focalized.Falsity
( -- * Negative falsity
  Bot
, absurdN
  -- * Positive falsity
, Zero
, absurdP
) where

import Focalized.Polarity

-- Negative falsity

data Bot

instance Polarized N Bot where

absurdN :: Bot -> a
absurdN = \case


-- Positive falsity

data Zero

instance Polarized P Zero where

absurdP :: Zero -> a
absurdP = \case
