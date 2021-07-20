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
import Data.Profunctor
import Sequoia.Confunctor
import Sequoia.Conjunction
import Sequoia.Continuation as K
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Optic.Iso
import Sequoia.Optic.Lens
import Sequoia.Optic.Setter
import Sequoia.Polarity
import Sequoia.Profunctor.Coexponential
import Sequoia.Profunctor.Exponential
import Sequoia.Value as V

-- Subtraction

newtype Sub e r a b = Sub { getSub :: Coexp e r b a }
  deriving Contravariant via Confunctorially (Sub e r) a

instance Confunctor (Sub e r) where
  conmap f g = over _Coexponential (dimap g f)

instance Coexponential Sub where
  inCS = Sub
  exCS = getSub

instance (Pos a, Neg b) => Polarized P (Sub e r a b) where

type a ~-r = (r :: Type -> Type -> Type) a
type s-< b = s b

infixr 6 ~-
infixr 5 -<


sub :: (K.Representable k, V.Representable v, Conj c) => a ~-Sub (V.Rep v) (K.Rep k)-< b <-> v a `c` k b
sub = _Coexponential.(coerceV . recall >---< coerceK . forget <-> uncurryConj Coexp . (coerceV *** coerceK))

subA_ :: Lens (a ~-Sub e r-< b) (a' ~-Sub e' r-< b) (V e a) (V e' a')
subA_ = _Coexponential.recall_

subK_ :: Lens (a ~-Sub e r-< b) (a ~-Sub e r'-< b') (K r b) (K r' b')
subK_ = _Coexponential.forget_
