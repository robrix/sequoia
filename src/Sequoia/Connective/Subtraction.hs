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
import Sequoia.Connective.Negate
import Sequoia.Connective.Tensor
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Polarity
import Sequoia.Profunctor.ControlPassing
import Sequoia.Value as V

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


sub :: V.Representable v => v a ⊗ r -b <-> a ~-Sub (V.Rep v) r-< b
sub = (\ (a :⊗ k) -> Sub (coerceV a) (getNegate k)) <-> (\ (Sub a k) -> coerceV a :⊗ Negate k)
