module Focalized.Negate
( -- * Negate
  type (-)(..)
) where

import Focalized.CPS
import Focalized.Polarity

newtype r -a = Negate { getNegate :: r •a }

instance Neg a => Polarized P (r -a) where

infixr 9 -
