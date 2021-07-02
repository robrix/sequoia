module Focalized.Connective.Iff
( -- * Logical biconditional
  Iff(..)
, type (<~)
, type (~>)
) where

import Focalized.CPS
import Focalized.Function (type (~>))
import Focalized.Polarity

-- Logical biconditional

data Iff r a b
  = IffT a b
  | IffF (r •a) (r •b)

instance (Neg a, Neg b) => Polarized N (Iff r a b)

type a <~r = Iff r a

infixr 6 <~
