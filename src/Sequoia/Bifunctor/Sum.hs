module Sequoia.Bifunctor.Sum
( -- * Sum type
  type (+)(..)
  -- * Elimination
, runS
) where

import Data.Bifoldable
import Data.Bifunctor

-- Sum type

newtype a + b = S { getS :: forall t . (a -> t) -> (b -> t) -> t }
  deriving (Functor)

infixr 6 +

instance Bifoldable (+) where
  bifoldMap f g = runS f g

instance Bifunctor (+) where
  bimap f g s = S (\ l r -> runS (l . f) (r . g) s)


-- Elimination

runS :: (a -> t) -> (b -> t) -> (a + b -> t)
runS f g s = getS s f g
