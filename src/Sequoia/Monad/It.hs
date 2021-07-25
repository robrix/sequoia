{-# LANGUAGE TypeFamilies #-}
module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Construction
, it
, doneIt
, needIt
, tabulateIt
  -- * Elimination
, foldIt
, headIt
, tailIt
, indexIt
  -- * Computation
, simplifyIt
) where

import Control.Monad (ap)
import Data.Distributive
import Data.Function ((&))
import Data.Functor.Rep
import Data.Profunctor

-- Iteratees

-- | Böhm-Berarducci–encoded iteratee, based loosely on the one in @trifecta@.
newtype It r a = It (forall s . (a -> s) -> ((r -> s) -> s) -> s)

instance Profunctor It where
  dimap f g = foldIt (doneIt . g) (it . lmap f)

instance Functor (It r) where
  fmap = rmap

instance Applicative (It r) where
  pure = doneIt
  (<*>) = ap

instance Monad (It r) where
  m >>= f = foldIt f it m

instance Distributive (It r) where
  distribute = distributeRep
  collect = collectRep

instance Representable (It r) where
  type Rep (It r) = r
  tabulate = tabulateIt
  index = indexIt


-- Construction

it :: (r -> It r a) -> It r a
it k = It (\ p f -> f (foldIt p f . k))

doneIt :: a -> It r a
doneIt a = It (const . ($ a))


needIt :: (r -> Maybe a) -> It r a
needIt f = i where i = it (maybe i pure . f)


tabulateIt :: (r -> a) -> It r a
tabulateIt f = it (pure . f)


-- Elimination

foldIt :: (a -> o) -> ((r -> o) -> o) -> It r a -> o
foldIt p k (It r) = r p k

headIt :: It r a -> Maybe a
headIt = foldIt Just (const Nothing)

tailIt :: It r a -> Maybe (r -> It r a)
tailIt = either (const Nothing) Just . foldIt (Left . pure) (\ k -> Right (either id . (&) <*> k))


indexIt :: It r a -> (r -> a)
indexIt = flip (foldIt id . (&))


-- Computation

simplifyIt :: It r a -> r -> It r a
simplifyIt i r = foldIt (const i) ($ r) i
