module Sequoia.Connective.Subtraction
( -- * Subtraction
  Sub(..)
, type (~-)
, type (-<)
, sub
) where

import Data.Functor.Contravariant
import Sequoia.Bijection
import Sequoia.Confunctor
import Sequoia.Connective.Negate
import Sequoia.Connective.Tensor
import Sequoia.Functor.K
import Sequoia.Polarity

-- Subtraction

data Sub r a b = Sub { subA :: a, subK :: K r b }
  deriving Contravariant via Confunctorially (Sub r) a

instance Confunctor (Sub r) where
  conmap f g (Sub a k) = Sub (f a) (contramap g k)

instance (Pos a, Neg b) => Polarized P (Sub r a b) where

type a ~-r = Sub r a
type s-< b = s b

infixr 6 ~-
infixr 5 -<


sub :: a ⊗ r -b <-> a ~-r-< b
sub = (\ (a :⊗ k) -> Sub a (getNegate k)) <-> (\ (Sub a k) -> a :⊗ Negate k)
