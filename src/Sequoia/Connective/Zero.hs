module Sequoia.Connective.Zero
( -- * Positive falsity
  Zero
, absurdP
) where

import Sequoia.Polarity

-- Positive falsity

data Zero

instance Polarized P Zero where

absurdP :: Zero -> a
absurdP = \case
