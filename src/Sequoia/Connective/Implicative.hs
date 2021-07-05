module Sequoia.Connective.Implicative
( elimFun
  -- * Connectives
, module Sequoia.Connective.Function
, module Sequoia.Connective.Subtraction
) where

import Sequoia.Connective.Function
import Sequoia.Connective.Subtraction
import Sequoia.Continuation

elimFun :: Representable k => a ~~k~> b -> a ~-k-< b -> Rep k
elimFun f s = appFun f (subA s) • subK s
