module Sequoia.Profunctor.Exp.Quantified
( -- * Exponentials
  type (-->)(..)
) where

import qualified Control.Category as Cat
import           Data.Profunctor

-- Exponentials

newtype a --> b = Exp { getExp :: forall r . (b -> r) -> (a -> r) }
  deriving (Functor)

instance Cat.Category (-->) where
  id = Exp id
  f . g = Exp (getExp g . getExp f)

instance Profunctor (-->) where
  dimap f g (Exp r) = Exp (\ k -> r (k . g) . f)
