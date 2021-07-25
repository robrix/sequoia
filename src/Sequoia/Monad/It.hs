module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Construction
, it
, doneIt
  -- * Elimination
, foldIt
, headIt
, indexIt
  -- * Computation
, simplifyIt
) where

import Control.Comonad
import Control.Monad (ap)
import Data.Profunctor

-- Iteratees

-- | Böhm-Berarducci–encoded iteratee, based loosely on the one in @trifecta@.
newtype It r a = It (forall s . (a -> s) -> (a -> (r -> s) -> s) -> s)

instance Profunctor It where
  dimap f g = foldIt (doneIt . g) (lmap (lmap f) . it . g)

instance Functor (It r) where
  fmap = rmap

instance Applicative (It r) where
  pure = doneIt
  (<*>) = ap

instance Monad (It r) where
  m >>= f = foldIt f (it . headIt . f) m

instance Comonad (It r) where
  extract = headIt
  duplicate i = foldIt (const (pure i)) (const (it i)) i


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


indexIt :: It r a -> (r -> a)
indexIt i r = foldIt id (const ($r)) i


-- Computation

simplifyIt :: It r a -> r -> It r a
simplifyIt it r = foldIt (const it) (const ($ r)) it
