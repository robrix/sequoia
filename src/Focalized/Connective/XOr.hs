module Focalized.Connective.XOr
( -- * Exclusive disjunction
  XOr(..)
, type (</)
, type (/>)
) where

import Focalized.Polarity
import Focalized.Subtraction
import Focalized.Up

-- Exclusive disjunction

newtype XOr r a b = XOr { getXOr :: Either (a ~-r-< Up b) (b ~-r-< Up a) }

instance (Pos a, Pos b) => Polarized P (XOr r a b)

type a </r = XOr r a
type r/> b = r b

infixr 6 </
infixr 5 />
