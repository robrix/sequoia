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

import           Data.Kind (Type)
import           Data.Profunctor
import           Fresnel.Lens
import           Sequoia.Polarity
import           Sequoia.Profunctor.Continuation
import qualified Sequoia.Profunctor.Exp as Coexp

-- Subtraction

data Sub r b a = (:>-) { subK :: b • r, subA :: a }
  deriving (Functor)

infixr 6 :>-

instance Profunctor (Sub r) where
  dimap f g (k :>- a) = lmap f k :>- g a

instance (Pos a, Neg b) => Polarized P (Sub r b a) where

type a >-r = (r :: Type -> Type -> Type) a
type s-~ b = s b

infixr 6 >-
infixr 5 -~


-- Elimination

runSubCoexp :: Sub r b a -> Coexp.Coexp r b a
runSubCoexp (k :>- a) = k Coexp.:>- a

appSub :: Sub r b a -> (b • r -> a • r) -> r
appSub (k :>- a) f = f k • a


-- Optics

subA_ :: Lens (b >-Sub r-~ a) (b >-Sub r-~ a') a a'
subA_ = lens subA (\ s subA -> s{ subA })

subK_ :: Lens (b >-Sub r-~ a) (b' >-Sub r'-~ a) (b • r) (b' • r')
subK_ = lens subK (\ s subK -> s{ subK })
