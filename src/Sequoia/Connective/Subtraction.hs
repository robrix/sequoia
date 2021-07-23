module Sequoia.Connective.Subtraction
( -- * Subtraction
  Sub(..)
, type (>-)
, type (-~)
  -- * Elimination
, subA
  -- * Optics
, subA_
, subK_
) where

import Data.Kind (Type)
import Data.Profunctor
import Sequoia.Optic.Getter
import Sequoia.Optic.Iso
import Sequoia.Optic.Lens
import Sequoia.Polarity
import Sequoia.Profunctor.Coexponential
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Subtraction

newtype Sub e r b a = Sub { getSub :: Coexp e r b a }
  deriving (Functor, Profunctor)

instance (Pos a, Neg b) => Polarized P (Sub e r b a) where

type a >-r = (r :: Type -> Type -> Type) a
type s-~ b = s b

infixr 6 >-
infixr 5 -~


-- Elimination

subA :: b >-Sub e r-~ a -> e ∘ a
subA = (^.subA_)


-- Optics

subA_ :: Lens (b >-Sub e r-~ a) (b >-Sub e' r-~ a') (e ∘ a) (e' ∘ a')
subA_ = coercedFrom Sub .recall_

subK_ :: Lens (b >-Sub e r-~ a) (b' >-Sub e r'-~ a) (b • r) (b' • r')
subK_ = coercedFrom Sub .forget_
