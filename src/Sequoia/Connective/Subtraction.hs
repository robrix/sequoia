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
import Sequoia.Confunctor
import Sequoia.Conjunction
import Sequoia.Continuation as K
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Optic.Iso
import Sequoia.Optic.Lens
import Sequoia.Polarity
import Sequoia.Profunctor.Coexponential
import Sequoia.Value as V

-- Subtraction

newtype Sub e r a b = Sub { getSub :: Coexp e r b a }
  deriving Contravariant via Confunctorially (Sub e r) a
  deriving Confunctor via Flip (Coexp e r)

instance Coexponential Sub where
  inCoexp = fmap Sub . Coexp
  exCoexp = (recall &&& forget) . getSub

instance (Pos a, Neg b) => Polarized P (Sub e r a b) where

type a ~-r = (r :: Type -> Type -> Type) a
type s-< b = s b

infixr 6 ~-
infixr 5 -<


sub :: (K.Representable k, V.Representable v, Conj c) => a ~-Sub (V.Rep v) (K.Rep k)-< b <-> v a `c` k b
sub = _Coexponential.(coerceV . fst >---< coerceK . snd <-> coerceConj . (coerceV *** coerceK))

subA_ :: Lens (a ~-Sub e r-< b) (a' ~-Sub e' r-< b) (V e a) (V e' a')
subA_ = _Coexponential._fst

subK_ :: Lens (a ~-Sub e r-< b) (a ~-Sub e r'-< b') (K r b) (K r' b')
subK_ = _Coexponential._snd
