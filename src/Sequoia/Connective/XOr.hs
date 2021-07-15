module Sequoia.Connective.XOr
( -- * Exclusive disjunction
  XOr(..)
, type (</)
, type (/>)
) where

import Sequoia.Connective.Subtraction
import Sequoia.Connective.Sum
import Sequoia.Connective.Up
import Sequoia.Polarity

-- Exclusive disjunction

newtype XOr r a b = XOr { getXOr :: (a ~-r-< Up b) ⊕ (b ~-r-< Up a) }

instance (Pos a, Pos b) => Polarized P (XOr r a b)

type a </r = XOr r a
type x/> b = x b

infixr 6 </
infixr 5 />
