module Sequoia.Connective.Implicative
( elimFun
  -- * Connectives
, module Sequoia.Connective.Function
, module Sequoia.Connective.Subtraction
) where

import Sequoia.Conjunction
import Sequoia.Connective.Function
import Sequoia.Connective.Subtraction
import Sequoia.Continuation

elimFun :: Representable k => a ~~k~> b -> a ~-k-< b -> Rep k
elimFun f (Sub s) = appFun f (exl s) • coerceK (exr s)
