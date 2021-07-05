module Sequoia.Connective.Subtraction
( -- * Subtraction
  Sub(..)
, type (~-)
, type (-<)
, sub
) where

import Sequoia.Connective.Negate
import Sequoia.Connective.Tensor
import Sequoia.Polarity

-- Subtraction

newtype Sub k a b = Sub { getSub :: a ⊗ k -b }

instance (Pos a, Neg b) => Polarized P (Sub k a b) where

type a ~-k = Sub k a
type s-< b = s b

infixr 6 ~-
infixr 5 -<


sub :: a ⊗ k -b -> a ~-k-< b
sub = Sub
