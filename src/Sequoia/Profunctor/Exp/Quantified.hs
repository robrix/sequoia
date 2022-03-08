module Sequoia.Profunctor.Exp.Quantified
( -- * Exponentials
  type (-->)(..)
  -- * Construction
, exp
  -- * Elimination
, (#)
  -- * Coexponentials
, type (>--)(..)
  -- * Computation
, cocurry
) where

import qualified Control.Category as Cat
import           Data.Profunctor
import           Prelude hiding (exp)

-- Exponentials

newtype a --> b = Exp { getExp :: forall r . (b -> r) -> (a -> r) }
  deriving (Functor)

infixr 0 -->

instance Cat.Category (-->) where
  id = Exp id
  f . g = Exp (getExp g . getExp f)

instance Profunctor (-->) where
  dimap f g (Exp r) = Exp (\ k -> r (k . g) . f)


-- Construction

exp :: (a -> b) -> (a --> b)
exp f = Exp (. f)


-- Elimination

(#) :: (a --> b) -> (a -> b)
f # a = getExp f id a

infixl 9 #


-- Coexponentials

data b >-- a = (:>--) { coreturn :: forall r . b -> r, coconst :: a }
  deriving (Functor)

infixr 0 >--, :>--

instance Profunctor (>--) where
  dimap f g (b :>-- a) = lmap f b :>-- g a


-- Computation

cocurry :: (c --> Either a b) -> ((b >-- c) --> a)
cocurry f = Exp (\ k (b :>-- c) -> getExp f (either k b) c)
