{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Negation
( -- * Not
  type (¬)(..)
  -- * Negate
, type (-)(..)
  -- * Negative double negation
, notNegate
, getNotNegate
, type (¬-)
  -- * Positive double negation
, negateNot
, getNegateNot
, type (-¬)
) where

import Sequoia.Continuation
import Sequoia.Functor.K
import Sequoia.Polarity

-- Not

newtype r ¬a = Not { getNot :: K r a }
  deriving (Continuation r, Contravariant, Representable)

instance Pos a => Polarized N (k ¬a) where

infixr 9 ¬


-- Negate

newtype r -a = Negate { getNegate :: K r a }
  deriving (Continuation r, Contravariant, Representable)

instance Neg a => Polarized P (k -a) where

infixr 9 -


-- Negative double negation

notNegate :: K r **a -> r ¬-a
notNegate = Not . contramap getNegate

getNotNegate :: r ¬-a -> K r **a
getNotNegate = contramap Negate . getNot


type r ¬-a = r ¬(r -a)

infixr 9 ¬-


-- Positive double negation

negateNot :: K r **a -> r -¬a
negateNot = Negate . contramap getNot

getNegateNot :: r -¬a -> K r **a
getNegateNot = contramap Not . getNegate


type r -¬a = r -(r ¬a)

infixr 9 -¬
