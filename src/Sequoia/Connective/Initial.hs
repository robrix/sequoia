module Sequoia.Connective.Initial
( -- * Adjunction
  leftAdjunct
, rightAdjunct
  -- * Connectives
, module Sequoia.Connective.NotUntrue
, module Sequoia.Connective.Negate
) where

import Sequoia.Connective.Negate
import Sequoia.Connective.NotUntrue
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Adjunction

leftAdjunct :: (Negate e a r -> b) -> (a • r -> NotUntrue e b)
leftAdjunct f a = NotUntrue (V (\ e -> f (Negate e a)))

rightAdjunct :: (a • r -> NotUntrue e b) -> (Negate e a r -> b)
rightAdjunct f a = negateE a ∘ runNotUntrue (f (negateK a))
