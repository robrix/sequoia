module Focalized.Connective.Iff
( -- * Logical biconditional
  Iff(..)
, type (<~)
, type (~>)
) where

import Focalized.CPS

-- Logical biconditional

data Iff r a b
  = IffT a b
  | IffF (r •a) (r •b)

type a <~r = Iff r a
type r~> b = r b

infixr 6 <~
infixr 5 ~>
