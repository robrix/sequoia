{-# LANGUAGE UndecidableInstances #-}
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
import Data.Functor.Contravariant.Adjunction
import Data.Functor.Contravariant.Rep (Representable)
import Sequoia.Functor.Continuation
import Sequoia.Polarity

-- Not

newtype Not r a = Not { getNot :: K r a }
  deriving (Contravariant, Representable)

instance Pos a => Polarized N (Not r a) where

instance Adjunction (Negate r) (Not r) where
  unit   a = Not    (K (•- a))
  counit a = Negate (K (•¬ a))
  leftAdjunct  f a = Not    (K ((•- a) . f))
  rightAdjunct f a = Negate (K ((•¬ a) . f))


type (¬) = Not

infixr 9 ¬


(•¬) :: Not r a -> (a -> r)
(•¬) = (•) . getNot

infixl 7 •¬


-- Negate

newtype Negate r a = Negate { getNegate :: K r a }
  deriving (Contravariant, Representable)

instance Neg a => Polarized P (Negate r a) where

instance Adjunction (Not r) (Negate r) where
  unit   a = Negate (K (•¬ a))
  counit a = Not    (K (•- a))
  leftAdjunct  f a = Negate (K ((•¬ a) . f))
  rightAdjunct f a = Not    (K ((•- a) . f))


type (-) = Negate

infixr 9 -


(•-) :: Negate r a -> (a -> r)
(•-) = (•) . getNegate

infixl 7 •-


-- Negative double negation

notNegate :: K r (K r a) -> r ¬-a
notNegate = Not . contramap getNegate

getNotNegate :: r ¬-a -> K r (K r a)
getNotNegate = contramap Negate . getNot


type r ¬-a = r ¬(r -a)

infixr 9 ¬-


-- Positive double negation

negateNot :: K r (K r a) -> r -¬a
negateNot = Negate . contramap getNot

getNegateNot :: r -¬a -> K r (K r a)
getNegateNot = contramap Not . getNegate


type r -¬a = r -(r ¬a)

infixr 9 -¬
