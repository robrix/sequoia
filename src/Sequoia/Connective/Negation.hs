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

import Data.Profunctor
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Sequoia.Continuation
import Sequoia.Polarity

-- Not

newtype (k ¬a) z = Not { getNot :: k a z }
  deriving (Applicative, Continuation, Functor, Profunctor, Representable, Strong)

instance Sieve k f => Sieve ((¬) k) f where
  sieve = sieve . getNot

instance Pos a => Polarized N ((k ¬a) z) where

infixr 9 ¬


-- Negate

newtype (k -a) z = Negate { getNegate :: k a z }
  deriving (Applicative, Continuation, Functor, Profunctor, Representable, Strong)

instance Sieve k f => Sieve ((-) k) f where
  sieve = sieve . getNegate

instance Neg a => Polarized P ((k -a) z) where

infixr 9 -


-- Negative double negation

notNegate :: Profunctor k => k **a -> k ¬-a
notNegate = Not . lmap getNegate

getNotNegate :: Profunctor k => k ¬-a -> k **a
getNotNegate = lmap Negate . getNot


type k ¬-a = (k ¬(k -a) ()) ()

infixr 9 ¬-


-- Positive double negation

negateNot :: Profunctor k => k **a -> k -¬a
negateNot = Negate . lmap getNot

getNegateNot :: Profunctor k => k -¬a -> k **a
getNegateNot = lmap Not . getNegate


type k -¬a = (k -(k ¬a) ()) ()

infixr 9 -¬
