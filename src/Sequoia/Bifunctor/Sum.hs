module Sequoia.Bifunctor.Sum
( -- * Sum type
  type (+)(..)
  -- * Construction
, inSl
, inSr
  -- * Elimination
, runS
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable

-- Sum type

newtype a + b = S { getS :: forall t . (a -> t) -> (b -> t) -> t }
  deriving (Functor)

infixr 6 +

instance Bifoldable (+) where
  bifoldMap f g = runS f g

instance Bifunctor (+) where
  bimap f g s = S (\ l r -> runS (l . f) (r . g) s)

instance Bitraversable (+) where
  bitraverse f g = runS (fmap inSl . f) (fmap inSr . g)


-- Construction

inSl :: a -> a + b
inSl a = S (\ l _ -> l a)

inSr :: b -> a + b
inSr b = S (\ _ r -> r b)


-- Elimination

runS :: (a -> t) -> (b -> t) -> (a + b -> t)
runS f g s = getS s f g
