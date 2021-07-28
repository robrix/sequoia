module Sequoia.Bifunctor.Sum
( -- * Sum type
  type (+)(..)
  -- * Elimination
, runS
) where

import Data.Bifunctor
import Sequoia.Disjunction

-- Sum type

newtype a + b = S { getS :: forall t . (a -> t) -> (b -> t) -> t }
  deriving (Functor)

infixr 6 +

instance Bifunctor (+) where
  bimap f g (S s) = S (\ l r -> s (l . f) (r . g) )

instance Disj (+) where
  inl a = S (\ f _ -> f a)
  inr b = S (\ _ g -> g b)
  (<-->) = runS


-- Elimination

runS :: (a -> t) -> (b -> t) -> (a + b -> t)
runS f g s = getS s f g
