module Sequoia.Monad.It
( -- * Iteratees
  It(..)
, ItM(..)
  -- * Construction
, rollIt
, doneIt
, needIt
, tabulateIt
  -- * Elimination
, foldIt
, runIt
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
, Enumeratee(..)
, take
) where

import Control.Applicative (Alternative(..), Applicative(liftA2))
import Control.Monad (ap, guard, (<=<))
import Prelude hiding (any, take)

-- Iteratees

-- | Iteratees, based loosely on the one in @trifecta@.
data It r m a
  = Done a
  | Roll (r -> m (It r m a))

instance Functor m => Functor (It r m) where
  fmap f = \case
    Done a -> Done (f a)
    Roll r -> Roll (fmap (fmap f) . r)

instance Functor m => Applicative (It r m) where
  pure = doneIt
  (<*>) = ap

instance Applicative m => Alternative (It r m) where
  empty = rollIt (const (pure empty))
  i@Done{} <|> _        = i
  _        <|> j@Done{} = j
  Roll i   <|> Roll j   = Roll (liftA2 (liftA2 (<|>)) i j)

instance Functor m => Monad (It r m) where
  m >>= f = go m
    where
    go = \case
      Done a -> f a
      Roll r -> Roll (fmap go . r)


newtype ItM r m a = ItM { getItM :: m (It r m a) }
  deriving (Functor)

instance Applicative m => Applicative (ItM r m) where
  pure = ItM . pure . pure
  ItM f <*> ItM a = ItM (liftA2 (<*>) f a)

instance Monad m => Monad (ItM r m) where
  ItM m >>= f = ItM (go m)
    where
    go m = m >>= \case
      Done a -> getItM (f a)
      Roll r -> pure (Roll (go . r))


-- Construction

rollIt :: (r -> m (It r m a)) -> It r m a
rollIt = Roll

doneIt :: a -> It r m a
doneIt = Done


needIt :: Applicative m => (r -> Maybe a) -> It r m a
needIt f = i where i = rollIt (pure . maybe i pure . f)


tabulateIt :: Applicative m => (r -> a) -> It r m a
tabulateIt f = rollIt (pure . pure . f)


-- Elimination

foldIt :: Monad m => (a -> m s) -> ((r -> m s) -> m s) -> (It r m a -> m s)
foldIt p k = go where go = runIt p (k . fmap (>>= go))

runIt :: (a -> m s) -> ((r -> m (It r m a)) -> m s) -> (It r m a -> m s)
runIt p k = \case
  Done a -> p a
  Roll r -> k r


evalIt :: Monad m => It (Maybe r) m a -> m a
evalIt = runIt pure (evalIt <=< ($ Nothing))


-- Computation

simplifyIt :: Monad m => It r m a -> r -> m (It r m a)
simplifyIt i r = foldIt (const (pure i)) ($ r) i


-- Parsing

any :: Applicative m => It (Maybe a) m a
any = rollIt (pure . maybe empty pure)

satisfy :: Applicative m => (a -> Bool) -> It (Maybe a) m a
satisfy p = rollIt (pure . maybe empty (\ c -> c <$ guard (p c)))

eof :: Applicative m => It (Maybe a) m ()
eof = rollIt (pure . maybe (pure ()) (const empty))


getLineIt :: Applicative m => It (Maybe Char) m String
getLineIt = loop id
  where
  loop = rollIt . fmap pure . check
  check acc (Just c)
    | c /= '\n' = loop (acc . (c:))
  check acc _   = pure (acc [])

getLinesIt :: Applicative m => It (Maybe Char) m [String]
getLinesIt = loop []
  where
  loop acc = getLineIt >>= check acc
  check acc "" = pure (reverse acc)
  check acc l  = loop (l:acc)


-- Enumerators

newtype Enumerator i m o = Enumerator { getEnumerator :: It i m o -> m (It i m o) }


enumerateList :: Monad m => [r] -> Enumerator (Maybe r) m a
enumerateList = Enumerator . go
  where
  go []     = pure
  go (c:cs) = \ i -> runIt (const (pure i)) (\ k -> go cs =<< k (Just c)) i


-- Enumeratees

newtype Enumeratee i o m a = Enumeratee { getEnumeratee :: It i m a -> It o m (It i m a) }

take :: Functor m => Int -> Enumeratee i i m o
take = Enumeratee . go
  where
  go n
    | n <= 0    = pure
    | otherwise = \case
      i@Done{} -> pure i
      Roll r   -> rollIt (fmap (go (n - 1)) . r)
