module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Construction
, it
, doneIt
, needIt
, wantIt
  -- * Elimination
, foldIt
, headIt
, tailIt
, indexIt
  -- * Computation
, simplifyIt
) where

import Control.Monad (ap)
import Data.Function ((&))
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


-- Construction

it :: a -> (r -> It r a) -> It r a
it a k = It (\ p f -> f a (foldIt p f . k))

doneIt :: a -> It r a
doneIt a = It (const . ($ a))


needIt :: a -> (r -> Maybe a) -> It r a
needIt a f = i where i = it a (maybe i pure . f)

wantIt :: a -> (r -> Either a a) -> It r a
wantIt a f = it a k where k = either (`it` k) pure . f


-- Elimination

foldIt :: (a -> o) -> (a -> (r -> o) -> o) -> It r a -> o
foldIt p k (It r) = r p k

headIt :: It r a -> a
headIt = foldIt id const

tailIt :: It r a -> Maybe (r -> It r a)
tailIt = foldIt (const Nothing) (\ a k -> Just (maybe (pure a) . (&) <*> k))


indexIt :: It r a -> (r -> a)
indexIt i r = foldIt id (const ($r)) i


-- Computation

simplifyIt :: It r a -> r -> It r a
simplifyIt it r = foldIt (const it) (const ($ r)) it
