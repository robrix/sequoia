module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Elimination
, foldIt
) where

-- Iteratees

-- | Böhm-Berarducci–encoded iteratee, based loosely on the one in @trifecta@.
newtype It r a = It (forall s . (a -> s) -> (a -> (r -> s) -> s) -> s)


-- Elimination

foldIt :: (a -> o) -> (a -> (r -> o) -> o) -> It r a -> o
foldIt p k (It r) = r p k
