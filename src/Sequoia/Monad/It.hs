module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Construction
, it
, doneIt
  -- * Elimination
, foldIt
, headIt
) where

import Data.Profunctor

-- Iteratees

-- | Böhm-Berarducci–encoded iteratee, based loosely on the one in @trifecta@.
newtype It r a = It (forall s . (a -> s) -> (a -> (r -> s) -> s) -> s)

instance Profunctor It where
  dimap f g = foldIt (doneIt . g) (lmap (lmap f) . it . g)

instance Functor (It r) where
  fmap = rmap


-- Construction

it :: a -> (r -> It r a) -> It r a
it a k = It (\ p f -> f a (foldIt p f . k))

doneIt :: a -> It r a
doneIt a = It (const . ($ a))


-- Elimination

foldIt :: (a -> o) -> (a -> (r -> o) -> o) -> It r a -> o
foldIt p k (It r) = r p k

headIt :: It r a -> a
headIt = foldIt id const
