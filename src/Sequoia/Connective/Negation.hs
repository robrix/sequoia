{-# LANGUAGE TypeFamilies #-}
module Sequoia.Connective.Negation
( -- * Negative double negation
  notNegate
, getNotNegate
  -- * Positive double negation
, negateNot
, getNegateNot
  -- * Connectives
, module Sequoia.Connective.Not
, module Sequoia.Connective.Negate
) where

import Data.Profunctor
import Sequoia.Connective.Negate
import Sequoia.Connective.Not
import Sequoia.Profunctor.Continuation

-- Negative double negation

notNegate :: a • r • r -> Not r (Negate e r a)
notNegate = Not . lmap getNegate

getNotNegate :: Not r (Negate e r a) -> a • r • r
getNotNegate = lmap Negate . getNot


-- Positive double negation

negateNot :: a • r • r -> Negate e r (Not r a)
negateNot = Negate . lmap getNot

getNegateNot :: Negate e r (Not r a) -> a • r • r
getNegateNot = lmap Not . getNegate
