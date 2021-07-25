module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Construction
, it
  -- * Elimination
, foldIt
) where

-- Iteratees

-- | Böhm-Berarducci–encoded iteratee, based loosely on the one in @trifecta@.
newtype It r a = It (forall s . (a -> s) -> (a -> (r -> s) -> s) -> s)


-- Construction

it :: a -> (r -> It r a) -> It r a
it a k = It (\ p f -> f a (foldIt p f . k))


-- Elimination

foldIt :: (a -> o) -> (a -> (r -> o) -> o) -> It r a -> o
foldIt p k (It r) = r p k
