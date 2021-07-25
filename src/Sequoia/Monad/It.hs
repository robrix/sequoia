{-# LANGUAGE TypeFamilies #-}
module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Construction
, it
, doneIt
, needIt
, tabulateIt
, evalItString
  -- * Elimination
, foldIt
, headIt
, tailIt
, indexIt
  -- * Computation
, simplifyIt
, getLineIt
, getLinesIt
) where

import Control.Monad (ap)
import Data.Distributive
import Data.Function ((&))
import Data.Functor.Rep
import Data.Maybe (listToMaybe)
import Data.Profunctor

-- Iteratees

-- | Scott–encoded iteratee, based loosely on the one in @trifecta@.
newtype It r a = It { runIt :: forall s . (a -> s) -> ((r -> It r a) -> s) -> s }

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
it k = It (const ($ k))

doneIt :: a -> It r a
doneIt a = It (const . ($ a))


needIt :: (r -> Maybe a) -> It r a
needIt f = i where i = it (maybe i pure . f)


tabulateIt :: (r -> a) -> It r a
tabulateIt f = it (pure . f)


evalItString :: String -> It (Maybe Char) a -> a
evalItString = foldIt id . (&) . listToMaybe


-- Elimination

foldIt :: (a -> s) -> ((r -> s) -> s) -> It r a -> s
foldIt p k = go where go r = runIt r p (k . fmap go)

headIt :: It r a -> Maybe a
headIt = foldIt Just (const Nothing)

tailIt :: It r a -> Maybe (r -> It r a)
tailIt = either (const Nothing) Just . foldIt (Left . pure) (\ k -> Right (either id . (&) <*> k))


indexIt :: It r a -> (r -> a)
indexIt = flip (foldIt id . (&))


-- Computation

simplifyIt :: It r a -> r -> It r a
simplifyIt i r = foldIt (const i) ($ r) i


getLineIt :: It (Maybe Char) String
getLineIt = loop id
  where
  loop = it . check
  check acc (Just c)
    | c /= '\n' = loop (acc . (c:))
  check acc _   = pure (acc [])

getLinesIt :: It (Maybe Char) [String]
getLinesIt = loop []
  where
  loop acc = getLineIt >>= check acc
  check acc "" = pure (reverse acc)
  check acc l  = loop (l:acc)
