module Sequoia.Connective.Final
( -- * Assertion
  leftAdjunct
, rightAdjunct
  -- * Connectives
, module Sequoia.Connective.Not
, module Sequoia.Connective.True
) where

import Control.Category ((<<<))
import Data.Profunctor
import Sequoia.Connective.Bottom
import Sequoia.Connective.Not
import Sequoia.Connective.True
import Sequoia.Profunctor.Continuation

-- Adjunction

leftAdjunct :: (True r a -> b • r) -> (a -> Not b r)
leftAdjunct f a = Not (rmap Bottom (f (true a)))

rightAdjunct :: (a -> Not b r) -> (True r a -> b • r)
rightAdjunct f a = trueK a <<< rmap absurdN (getNot (f (trueA a)))
