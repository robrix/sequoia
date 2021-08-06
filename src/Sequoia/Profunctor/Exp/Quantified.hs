module Sequoia.Profunctor.Exp.Quantified
( -- * Exponentials
  type (-->)(..)
  -- * Construction
, exp
  -- * Elimination
, (#)
) where

import qualified Control.Category as Cat
import           Data.Profunctor
import           Prelude hiding (exp)

-- Exponentials

newtype a --> b = Exp { getExp :: forall r . (b -> r) -> (a -> r) }
  deriving (Functor)

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
(#) = (`getExp` id)

infixl 9 #
