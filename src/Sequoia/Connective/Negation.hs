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

notNegate :: a •• r -> Not r (Negate e r a)
notNegate = Not . lmap negateK

getNotNegate :: e -> Not r (Negate e r a) -> a •• r
getNotNegate e = lmap (Negate e) . getNot


-- Positive double negation

negateNot :: e -> a •• r -> Negate e r (Not r a)
negateNot e = Negate e . lmap getNot

getNegateNot :: Negate e r (Not r a) -> a •• r
getNegateNot = lmap Not . negateK
