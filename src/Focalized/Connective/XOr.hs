module Focalized.Connective.XOr
( -- * Exclusive disjunction
  XOr(..)
, type (</)
, type (/>)
) where

import Focalized.CPS
import Focalized.Polarity

-- Exclusive disjunction

data XOr r a b
  = XOrL a (r •b)
  | XOrR b (r •a)

instance (Pos a, Pos b) => Polarized P (XOr r a b)

type a </r = XOr r a
type r/> b = r b

infixr 6 </
infixr 5 />
