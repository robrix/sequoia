module Sequoia.Connective.Subtraction
( -- * Subtraction
  Sub(..)
, type (>-)
, type (-~)
  -- * Elimination
, runSubCoexp
, appSub
  -- * Optics
, subA_
, subK_
) where

import Data.Kind (Type)
import Data.Profunctor
import Fresnel.Lens
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exp (Coexp(..))

-- Subtraction

data Sub r b a = (:-<) { subA :: a, subK :: b • r }
  deriving (Functor)

infixr 6 :-<

instance Profunctor (Sub r) where
  dimap f g (a :-< k) = g a :-< lmap f k

instance (Pos a, Neg b) => Polarized P (Sub r b a) where

type a >-r = (r :: Type -> Type -> Type) a
type s-~ b = s b

infixr 6 >-
infixr 5 -~


-- Elimination

runSubCoexp :: Sub r b a -> Coexp r b a
runSubCoexp (a :-< k) = k :>- a

appSub :: Sub r b a -> (b • r -> a • r) -> r
appSub (a :-< k) f = f k • a


-- Optics

subA_ :: Lens (b >-Sub r-~ a) (b >-Sub r-~ a') a a'
subA_ = lens subA (\ s subA -> s{ subA })

subK_ :: Lens (b >-Sub r-~ a) (b' >-Sub r'-~ a) (b • r) (b' • r')
subK_ = lens subK (\ s subK -> s{ subK })
