module Sequoia.Connective.Subtraction
( -- * Subtraction
  Sub(..)
, type (~-)
, type (-<)
, sub
) where

import Control.Arrow ((&&&))
import Data.Functor.Contravariant
import Data.Kind (Type)
import Sequoia.Bijection
import Sequoia.Confunctor
import Sequoia.Connective.Assertion as Assertion
import Sequoia.Connective.Negate
import Sequoia.Connective.Tensor
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Polarity
import Sequoia.Profunctor.ControlPassing

-- Subtraction

data Sub e r a b = Sub { subA :: V e a, subK :: K r b }
  deriving Contravariant via Confunctorially (Sub e r) a

instance Confunctor (Sub e r) where
  conmap f g (Sub a k) = Sub (f <$> a) (contramap g k)

instance ControlStoring Sub where
  inCS = uncurry Sub
  exCS = subA &&& subK

instance (Pos a, Neg b) => Polarized P (Sub e r a b) where

type a ~-r = (r :: Type -> Type -> Type) a
type s-< b = s b

infixr 6 ~-
infixr 5 -<


sub :: True e a ⊗ r -b <-> a ~-Sub e r-< b
sub = (\ (a :⊗ k) -> Sub (getTrue a) (getNegate k)) <-> (\ (Sub a k) -> Assertion.True a :⊗ Negate k)
