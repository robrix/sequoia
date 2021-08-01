module Sequoia.Connective.Subtraction
( -- * Subtraction
  Sub(..)
, type (>-)
, type (-~)
  -- * Optics
, subA_
, subK_
) where

import Data.Kind (Type)
import Data.Profunctor
import Fresnel.Lens
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Subtraction

data Sub e r b a = (:-<) { subA :: e ∘ a, subK :: b • r }
  deriving (Functor)

infixr 6 :-<

instance Profunctor (Sub e r) where
  dimap f g (a :-< k) = rmap g a :-< lmap f k

instance (Pos a, Neg b) => Polarized P (Sub e r b a) where

type a >-r = (r :: Type -> Type -> Type) a
type s-~ b = s b

infixr 6 >-
infixr 5 -~


-- Optics

subA_ :: Lens (b >-Sub e r-~ a) (b >-Sub e' r-~ a') (e ∘ a) (e' ∘ a')
subA_ = lens subA (\ s subA -> s{ subA })

subK_ :: Lens (b >-Sub e r-~ a) (b' >-Sub e r'-~ a) (b • r) (b' • r')
subK_ = lens subK (\ s subK -> s{ subK })
