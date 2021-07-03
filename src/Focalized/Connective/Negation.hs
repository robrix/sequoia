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

-- Negative double negation

notNegate :: Contravariant k => k (k a) -> k ¬-a
notNegate = Not . contramap getNegate

getNotNegate :: Contravariant k => k ¬-a -> k (k a)
getNotNegate = contramap Negate . getNot


type k ¬-a = k ¬k -a

infixr 9 ¬-


-- Positive double negation

negateNot :: Contravariant k => k (k a) -> k -¬a
negateNot = Negate . contramap getNot

getNegateNot :: Contravariant k => k -¬a -> k (k a)
getNegateNot = contramap Not . getNegate


type r -¬a = r -r ¬a

infixr 9 -¬
