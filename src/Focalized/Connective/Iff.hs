module Focalized.Connective.Iff
( -- * Logical biconditional
  Iff(..)
, type (<~)
, type (~>)
) where

import Focalized.Down
import Focalized.Function
import Focalized.Polarity

-- Logical biconditional

newtype Iff r a b = Iff { getIff :: (Down a ~~r~> b, Down b ~~r~> a) }

instance (Neg a, Neg b) => Polarized N (Iff r a b)

type a <~r = Iff r a

infixr 6 <~
