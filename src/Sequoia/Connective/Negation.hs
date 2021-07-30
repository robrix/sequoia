{-# LANGUAGE TypeFamilies #-}
module Sequoia.Connective.Negation
( -- * Negative double negation
  notNegate
, getNotNegate
, type (¬-)
  -- * Positive double negation
, negateNot
, getNegateNot
, type (-¬)
  -- * Connectives
, module Sequoia.Connective.Not
, module Sequoia.Connective.Negate
) where

import Data.Profunctor
import Sequoia.Connective.Negate
import Sequoia.Connective.Not
import Sequoia.Profunctor.Continuation

-- Negative double negation

notNegate :: a • r • r -> r ¬-a
notNegate = Not . lmap getNegate

getNotNegate :: r ¬-a -> a • r • r
getNotNegate = lmap Negate . getNot


type r ¬-a = r ¬(r -a)

infixr 9 ¬-


-- Positive double negation

negateNot :: a • r • r -> r -¬a
negateNot = Negate . lmap getNot

getNegateNot :: r -¬a -> a • r • r
getNegateNot = lmap Not . getNegate


type r -¬a = r -(r ¬a)

infixr 9 -¬
