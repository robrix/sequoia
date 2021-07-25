{-# LANGUAGE TypeFamilies #-}
module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Construction
, rollIt
, doneIt
, needIt
, tabulateIt
  -- * Elimination
, foldIt
, runIt
, decomposeIt
, headIt
, tailIt
, indexIt
, evalIt
  -- * Computation
, simplifyIt
  -- * Parsing
, any
, satisfy
, eof
, getLineIt
, getLinesIt
  -- * Enumerators
, Enumerator(..)
, enumerateList
  -- * Enumeratees
, Enumeratee
) where

import Control.Applicative (Alternative(..))
import Control.Monad (ap, guard)
import Data.Distributive
import Data.Function ((&))
import Data.Functor.Rep
import Data.Profunctor
import Prelude hiding (any)

-- Iteratees

-- | Iteratees, based loosely on the one in @trifecta@.
data It r a
  = Done a
  | Roll (r -> It r a)

instance Profunctor It where
  dimap f g = foldIt (doneIt . g) (rollIt . lmap f)

instance Functor (It r) where
  fmap = rmap

instance Applicative (It r) where
  pure = doneIt
  (<*>) = ap

instance Alternative (It r) where
  empty = rollIt (const empty)
  i <|> j = runIt (const i) (\ ki -> runIt (const j) (\ kj -> rollIt (\ r -> ki r <|> kj r)) j) i

instance Monad (It r) where
  m >>= f = foldIt f rollIt m

instance Distributive (It r) where
  distribute = distributeRep
  collect = collectRep

instance Representable (It r) where
  type Rep (It r) = r
  tabulate = tabulateIt
  index = indexIt


-- Construction

rollIt :: (r -> It r a) -> It r a
rollIt = Roll

doneIt :: a -> It r a
doneIt = Done


needIt :: (r -> Maybe a) -> It r a
needIt f = i where i = rollIt (maybe i pure . f)


tabulateIt :: (r -> a) -> It r a
tabulateIt f = rollIt (pure . f)


-- Elimination

foldIt :: (a -> s) -> ((r -> s) -> s) -> (It r a -> s)
foldIt p k = go where go = runIt p (k . fmap go)

runIt :: (a -> s) -> ((r -> It r a) -> s) -> (It r a -> s)
runIt p k = \case
  Done a -> p a
  Roll r -> k r

decomposeIt :: It r a -> Either a (r -> It r a)
decomposeIt = runIt Left Right

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
any = rollIt (maybe empty pure)

satisfy :: (a -> Bool) -> It (Maybe a) a
satisfy p = rollIt (maybe empty (\ c -> c <$ guard (p c)))

eof :: It (Maybe a) ()
eof = rollIt (maybe (pure ()) (const empty))


getLineIt :: It (Maybe Char) String
getLineIt = loop id
  where
  loop = rollIt . check
  check acc (Just c)
    | c /= '\n' = loop (acc . (c:))
  check acc _   = pure (acc [])

getLinesIt :: It (Maybe Char) [String]
getLinesIt = loop []
  where
  loop acc = getLineIt >>= check acc
  check acc "" = pure (reverse acc)
  check acc l  = loop (l:acc)


-- Enumerators

newtype Enumerator i o = Enumerator { getEnumerator :: It i o -> It i o }


enumerateList :: [r] -> Enumerator (Maybe r) a
enumerateList = Enumerator . go
  where
  go []     = id
  go (c:cs) = runIt pure (\ k -> go cs (k (Just c)))


-- Enumeratees

type Enumeratee i o a = It i a -> It o (It i a)
