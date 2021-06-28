module Focalized.Negation
( -- * Negative double negation
  notNegate
, getNotNegate
, type (¬-)
  -- * Positive double negation
, negateNot
, getNegateNot
, type (-¬)
  -- * Not
, module Focalized.Not
  -- * Negate
, module Focalized.Negate
) where

import Data.Functor.Contravariant
import Focalized.CPS
import Focalized.Negate
import Focalized.Not

-- Negative double negation

notNegate :: r ••a -> r ¬-a
notNegate = Not . contramap getNegate

getNotNegate :: r ¬-a -> r ••a
getNotNegate = contramap Negate . getNot


type r ¬-a = r ¬r -a

infixr 9 ¬-


-- Positive double negation

negateNot :: r ••a -> r -¬a
negateNot = Negate . contramap getNot

getNegateNot :: r -¬a -> r ••a
getNegateNot = contramap Not . getNegate


type r -¬a = r -r ¬a

infixr 9 -¬
