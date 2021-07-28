module Sequoia.Bifunctor.Sum
( -- * Sum type
  type (+)(..)
  -- * Elimination
, runS
) where

import Data.Bifunctor

-- Sum type

newtype a + b = S { getS :: forall t . (a -> t) -> (b -> t) -> t }
  deriving (Functor)

infixr 6 +

instance Bifunctor (+) where
  bimap f g (S s) = S (\ l r -> s (l . f) (r . g) )


-- Elimination

runS :: (a -> t) -> (b -> t) -> (a + b -> t)
runS f g s = getS s f g
