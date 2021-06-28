module Focalized.Negate
( -- * Negate
  runNegate
, type (-)(..)
) where

import Focalized.CPS
import Focalized.Polarity

runNegate :: r -a -> (a -> r)
runNegate = runK . getNegate

newtype r -a = Negate { getNegate :: r •a }

instance Neg a => Polarized P (r -a) where

infixr 9 -
