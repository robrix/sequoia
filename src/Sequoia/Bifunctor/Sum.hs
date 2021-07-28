module Sequoia.Bifunctor.Sum
( -- * Sum type
  type (+)(..)
) where

-- Sum type

newtype a + b = S { getS :: forall t . (a -> t) -> (b -> t) -> t }
  deriving (Functor)

infixr 6 +
