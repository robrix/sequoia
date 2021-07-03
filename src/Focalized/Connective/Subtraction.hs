module Focalized.Connective.Subtraction
( -- * Subtraction
  Sub(..)
, type (~-)
, type (-<)
) where

import Focalized.Connective.Negate
import Focalized.Connective.Tensor
import Focalized.Polarity

-- Subtraction

newtype Sub k a b = Sub { getSub :: a ⊗ k -b }

instance (Pos a, Neg b) => Polarized P (Sub k a b) where

type a ~-k = Sub k a
type s-< b = s b

infixr 6 ~-
infixr 5 -<
