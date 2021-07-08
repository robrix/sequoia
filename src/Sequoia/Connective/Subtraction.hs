module Sequoia.Connective.Subtraction
( -- * Subtraction
  Sub(..)
, type (~-)
, type (-<)
, sub
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Sequoia.Bijection
import Sequoia.Confunctor
import Sequoia.Connective.Negate
import Sequoia.Connective.Tensor
import Sequoia.Polarity

-- Subtraction

data Sub k a b = Sub { subA :: a, subK :: k b () }
  deriving Contravariant via Confunctorially (Sub k) a

instance Profunctor k => Confunctor (Sub k) where
  conmap f g (Sub a k) = Sub (f a) (lmap g k)

instance (Pos a, Neg b) => Polarized P (Sub k a b) where

type a ~-k = Sub k a
type s-< b = s b

infixr 6 ~-
infixr 5 -<


sub :: a ⊗ (k -b) () <-> a ~-k-< b
sub = (\ (a :⊗ k) -> Sub a (getNegate k)) <-> (\ (Sub a k) -> a :⊗ Negate k)
