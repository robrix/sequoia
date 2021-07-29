{-# LANGUAGE TypeFamilies #-}
module Sequoia.Connective.Negation
( -- * Not
  Not(..)
, type (¬)
, (•¬)
  -- * Negate
, Negate(..)
, type (-)
, (•-)
  -- * Negative double negation
, notNegate
, getNotNegate
, type (¬-)
  -- * Positive double negation
, negateNot
, getNegateNot
, type (-¬)
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Not

newtype Not r a = Not { getNot :: a • r }

instance Contravariant (Not r) where
  contramap f = Not . lmap f . getNot

instance Pos a => Polarized N (Not r a) where


type (¬) = Not

infixr 9 ¬


(•¬) :: Not r a -> (a -> r)
(•¬) = (•) . getNot

infixl 7 •¬


-- Negate

newtype Negate r a = Negate { getNegate :: a • r }

instance Contravariant (Negate r) where
  contramap f = Negate . lmap f . getNegate

instance Neg a => Polarized P (Negate r a) where


type (-) = Negate

infixr 9 -


(•-) :: Negate r a -> (a -> r)
(•-) = (•) . getNegate

infixl 7 •-


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
