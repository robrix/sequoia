module Sequoia.Connective.Negation
( -- * Negative double negation
  notNegate
, getNotNegate
, type (¬-)
  -- * Positive double negation
, negateNot
, getNegateNot
, type (-¬)
  -- * Not
, module Sequoia.Connective.Not
  -- * Negate
, module Sequoia.Connective.Negate
) where

import Data.Functor.Contravariant
import Sequoia.Connective.Negate
import Sequoia.Connective.Not

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
