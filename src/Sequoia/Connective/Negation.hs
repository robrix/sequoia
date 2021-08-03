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
import Prelude hiding (negate)
import Sequoia.Connective.Negate
import Sequoia.Connective.Not
import Sequoia.Profunctor.Continuation

-- Negative double negation

notNegate :: a •• r -> Negate e a r ¬ r
notNegate = Not . lmap negateK

getNotNegate :: e -> Negate e a r ¬ r -> a •• r
getNotNegate e = lmap (negate e) . getNot


-- Positive double negation

negateNot :: e -> a •• r -> Negate e (a ¬ r) r
negateNot e = negate e . lmap getNot

getNegateNot :: Negate e (a ¬ r) r -> a •• r
getNegateNot = lmap Not . negateK
