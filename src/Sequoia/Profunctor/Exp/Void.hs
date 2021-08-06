module Sequoia.Profunctor.Exp.Void
( -- * Exponentials
  type (-->)(..)
  -- * Coexponentials
, type (>--)(..)
  -- * Computation
, cocurry
, uncocurry
, coap
) where

import qualified Control.Category as Cat
import           Data.Profunctor
import           Data.Void
import           Sequoia.Disjunction

-- Exponentials

newtype a --> b = Exp { getExp :: (b -> Void) -> (a -> Void) }
  deriving (Functor)

infixr 0 -->

instance Cat.Category (-->) where
  id = Exp id
  f . g = Exp (getExp g . getExp f)

instance Profunctor (-->) where
  dimap f g = Exp . dimap (lmap g) (lmap f) . getExp


-- Coexponentials

data b >-- a = (:>--) { coreturn :: b -> Void, coconst :: a }
  deriving (Functor)

infixr 0 >--, :>--

instance Profunctor (>--) where
  dimap f g (b :>-- a) = b . f :>-- g a


-- Computation

cocurry :: (c --> Either a b) -> ((b >-- c) --> a)
cocurry f = Exp (\ k (b :>-- c) -> getExp f (either k b) c)

uncocurry :: ((b >-- c) --> a) -> c --> Either a b
uncocurry f = Exp (\ k c -> getExp f (inlL k) (inrL k :>-- c))

coap :: c --> Either (b >-- c) b
coap = Exp (\ k -> inlL k . (inrL k :>--))
