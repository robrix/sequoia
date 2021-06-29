module Focalized.Negate
( -- * Negate
  runNegate
, appNegate
, type (-)(..)
) where

import Focalized.CPS
import Focalized.Polarity

runNegate :: r -a -> (a -> r)
runNegate = (•) . getNegate

appNegate :: a -> r -a -> r
appNegate = flip runNegate

newtype r -a = Negate { getNegate :: r •a }

instance Neg a => Polarized P (r -a) where

infixr 9 -
