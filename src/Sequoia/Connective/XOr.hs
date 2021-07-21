module Sequoia.Connective.XOr
( -- * Exclusive disjunction
  XOr(..)
, type (</)
, type (/>)
) where

import Data.Kind (Type)
import Sequoia.Connective.Subtraction
import Sequoia.Connective.Sum
import Sequoia.Connective.Up
import Sequoia.Polarity

-- Exclusive disjunction

newtype XOr e r a b = XOr { getXOr :: (Up a >-Sub e r-~ b) ⊕ (Up b >-Sub e r-~ a) }

instance (Pos a, Pos b) => Polarized P (XOr e r a b)

type a </r = (r :: Type -> Type -> Type) a
type x/> b = x b

infixr 6 </
infixr 5 />
