module Focalized.Negation
( -- * Not
  type (¬)(..)
, notNegate
, getNotNegate
, type (¬-)
  -- * Negate
, type (-)(..)
, negateNot
, getNegateNot
, type (-¬)
) where

import Data.Functor.Contravariant
import Focalized.CPS
import Focalized.Polarity

newtype r ¬a = Not    { getNot    :: r •a }

instance Pos a => Polarized N (r ¬a) where

notNegate :: r ••a -> r ¬-a
notNegate = Not . contramap getNegate

getNotNegate :: r ¬-a -> r ••a
getNotNegate = contramap Negate . getNot


type r ¬-a = r ¬r -a

infixr 9 ¬, ¬-


newtype r -a = Negate { getNegate :: r •a }

instance Neg a => Polarized P (r -a) where

negateNot :: r ••a -> r -¬a
negateNot = Negate . contramap getNot

getNegateNot :: r -¬a -> r ••a
getNegateNot = contramap Not . getNegate


type r -¬a = r -r ¬a

infixr 9 -, -¬
