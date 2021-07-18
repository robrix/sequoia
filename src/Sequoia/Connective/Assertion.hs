module Sequoia.Connective.Assertion
( -- * Yes
  Yes(..)
) where

import Sequoia.Functor.V
import Sequoia.Polarity

-- Yes

newtype Yes e a = Yes { getYes :: V e a }

instance Pos a => Polarized P (Yes e a) where
