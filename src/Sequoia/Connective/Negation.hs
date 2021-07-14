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
import Sequoia.Polarity

-- Not

newtype k ¬a = Not { getNot :: k a }
  deriving (Applicative, Continuation r, Contravariant, Functor, Representable)

instance Pos a => Polarized N (k ¬a) where

infixr 9 ¬


-- Negate

newtype k -a = Negate { getNegate :: k a }
  deriving (Applicative, Continuation r, Contravariant, Functor, Representable)

instance Neg a => Polarized P (k -a) where

infixr 9 -


-- Negative double negation

notNegate :: Contravariant k => k **a -> k ¬-a
notNegate = Not . contramap getNegate

getNotNegate :: Contravariant k => k ¬-a -> k **a
getNotNegate = contramap Negate . getNot


type k ¬-a = (k ¬(k -a))

infixr 9 ¬-


-- Positive double negation

negateNot :: Contravariant k => k **a -> k -¬a
negateNot = Negate . contramap getNot

getNegateNot :: Contravariant k => k -¬a -> k **a
getNegateNot = contramap Not . getNegate


type k -¬a = (k -(k ¬a))

infixr 9 -¬
