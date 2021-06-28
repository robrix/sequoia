module Focalized.Subtraction
( -- * Subtraction
  Sub(..)
, type (~-)
, type (-<)
) where

import Focalized.Negation
import Focalized.Polarity

-- Subtraction

data Sub r a b = Sub { subA :: !a, subK :: !(r -b) }

instance (Pos a, Neg b) => Polarized P (Sub r a b) where

type a ~-r = Sub r a
type r-< b = r b

infixr 6 ~-
infixr 5 -<
