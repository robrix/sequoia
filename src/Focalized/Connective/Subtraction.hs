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

newtype Sub r a b = Sub { getSub :: a ⊗ r -b }

instance (Pos a, Neg b) => Polarized P (Sub r a b) where

type a ~-r = Sub r a
type r-< b = r b

infixr 6 ~-
infixr 5 -<
