module Sequoia.Connective.Subtraction
( -- * Subtraction
  Sub(..)
, type (~-)
, type (-<)
, sub
, subA_
, subK_
) where

import Data.Functor.Contravariant
import Data.Kind (Type)
import Sequoia.Bijection
import Sequoia.Confunctor
import Sequoia.Conjunction
import Sequoia.Continuation as K
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Optic.Lens
import Sequoia.Polarity
import Sequoia.Profunctor.Coexponential
import Sequoia.Profunctor.ControlPassing
import Sequoia.Value as V

-- Subtraction

data Sub e r a b = Sub { subA :: V e a, subK :: K r b }
  deriving Contravariant via Confunctorially (Sub e r) a

instance Confunctor (Sub e r) where
  conmap f g (Sub a k) = Sub (f <$> a) (contramap g k)

instance ControlStoring Sub where
  inCS (Coexp a b) = Sub a b
  exCS = Coexp <$> subA <*> subK

instance (Pos a, Neg b) => Polarized P (Sub e r a b) where

type a ~-r = (r :: Type -> Type -> Type) a
type s-< b = s b

infixr 6 ~-
infixr 5 -<


sub :: (K.Representable k, V.Representable v, Conj c) => v a `c` k b <-> a ~-Sub (V.Rep v) (K.Rep k)-< b
sub = uncurryConj Sub . (coerceV *** coerceK) <-> coerceV . subA >---< coerceK . subK

subA_ :: Lens (a ~-Sub e r-< b) (a' ~-Sub e' r-< b) (V e a) (V e' a')
subA_ = lens subA (\ s subA -> s{ subA })

subK_ :: Lens (a ~-Sub e r-< b) (a ~-Sub e r'-< b') (K r b) (K r' b')
subK_ = lens subK (\ s subK -> s{ subK })
