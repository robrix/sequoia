module Sequoia.Connective.Assertion
( -- * Yes
  Yes(..)
) where

import Sequoia.Functor.V

-- Yes

newtype Yes e a = Yes { getYes :: V e a }
