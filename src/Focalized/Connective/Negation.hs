module Focalized.Connective.Negation
( -- * Negative double negation
  notNegate
, getNotNegate
, type (¬-)
  -- * Positive double negation
, negateNot
, getNegateNot
, type (-¬)
  -- * Not
, module Focalized.Connective.Not
  -- * Negate
, module Focalized.Connective.Negate
) where

import Data.Functor.Contravariant
import Focalized.Connective.Negate
import Focalized.Connective.Not
import Focalized.Continuation

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
