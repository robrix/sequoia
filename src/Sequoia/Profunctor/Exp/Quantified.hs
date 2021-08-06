module Sequoia.Profunctor.Exp.Quantified
( -- * Exponentials
  type (-->)(..)
) where

import Data.Profunctor

newtype a --> b = Exp { getExp :: forall r . (b -> r) -> (a -> r) }
  deriving (Functor)

instance Profunctor (-->) where
  dimap f g (Exp r) = Exp (\ k -> r (k . g) . f)
