module Focalized.Connective.Zero
( -- * Positive falsity
  Zero
, absurdP
) where

import Focalized.Polarity

-- Positive falsity

data Zero

instance Polarized P Zero where

absurdP :: Zero -> a
absurdP = \case
