{-# LANGUAGE TypeFamilies #-}
module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Construction
, it
, doneIt
, needIt
, tabulateIt
, enumerateList
  -- * Elimination
, foldIt
, runIt
, headIt
, tailIt
, indexIt
, evalIt
  -- * Computation
, simplifyIt
  -- * Parsing
, any
, satisfy
, getLineIt
, getLinesIt
) where

import Control.Applicative (Alternative(..))
import Control.Monad (ap, guard)
import Data.Distributive
import Data.Function ((&))
import Data.Functor.Rep
import Data.Profunctor
import Prelude hiding (any)

-- Iteratees

-- | Scott–encoded iteratee, based loosely on the one in @trifecta@.
newtype It r a = It { getIt :: forall s . (a -> s) -> ((r -> It r a) -> s) -> s }

instance Profunctor It where
  dimap f g = foldIt (doneIt . g) (it . lmap f)

instance Functor (It r) where
  fmap = rmap

instance Applicative (It r) where
  pure = doneIt
  (<*>) = ap

instance Alternative (It r) where
  empty = it (const empty)
  i <|> j = runIt (const i) (\ ki -> runIt (const j) (\ kj -> it (\ r -> ki r <|> kj r)) j) i

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


enumerateList :: [r] -> It (Maybe r) a -> It (Maybe r) a
enumerateList []     = id
enumerateList (c:cs) = runIt pure (\ k -> enumerateList cs (k (Just c)))


-- Elimination

foldIt :: (a -> s) -> ((r -> s) -> s) -> (It r a -> s)
foldIt p k = go where go = runIt p (k . fmap go)

runIt :: (a -> s) -> ((r -> It r a) -> s) -> (It r a -> s)
runIt p k i = getIt i p k

headIt :: It r a -> Maybe a
headIt = foldIt Just (const Nothing)

tailIt :: It r a -> Maybe (r -> It r a)
tailIt = runIt (const Nothing) Just


indexIt :: It r a -> (r -> a)
indexIt = flip (foldIt id . (&))


evalIt :: It (Maybe r) a -> a
evalIt = runIt id (evalIt . ($ Nothing))


-- Computation

simplifyIt :: It r a -> r -> It r a
simplifyIt i r = foldIt (const i) ($ r) i


-- Parsing

any :: It (Maybe a) a
any = it (maybe empty pure)

satisfy :: (Char -> Bool) -> It (Maybe Char) Char
satisfy p = it (maybe empty (\ c -> c <$ guard (p c)))


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
