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
, evalIt
  -- * Computation
, simplifyIt
  -- * Parsing
, getLineIt
, getLinesIt
  -- * Enumerators
, Enumerator(..)
, enumerateList
  -- * Enumeratees
, Enumeratee(..)
, take
) where

import Control.Comonad
import Control.Monad (ap, (<=<))
import Data.Profunctor
import Prelude hiding (any, take)

-- Iteratees

-- | Iteratees, based loosely on the one in @trifecta@.
data It m r a
  = Done a
  | Roll a (r -> m (It m r a))

instance Functor m => Profunctor (It m) where
  dimap f g = go
    where
    go = \case
      Done a   -> Done (g a)
      Roll a r -> Roll (g a) (fmap go . r . f)

instance Functor m => Functor (It m r) where
  fmap f = go
    where
    go = \case
      Done a   -> Done (f a)
      Roll a r -> Roll (f a) (fmap go . r)

instance Monad m => Applicative (It m r) where
  pure = doneIt
  (<*>) = ap

instance Monad m => Monad (It m r) where
  m >>= f = go m
    where
    go = \case
      Done a   -> f a
      Roll a k -> Roll (headIt (f a)) $ \ r -> do
        kr' <- k r
        case kr' of
          Done a'    -> simplifyIt (f a') r
          Roll a' k' -> do
            a'' <- indexIt (f a') r
            pure $ Roll a'' (pure . go <=< k')

instance Functor m => Comonad (It m r) where
  extract = headIt

  duplicate = \case
    i@Done{}     -> Done i
    i@(Roll _ k) -> Roll i (fmap duplicate . k)

  extend f = go
    where
    go = \case
      i@Done{}     -> Done (f i)
      i@(Roll _ k) -> Roll (f i) (fmap go . k)


-- Construction

rollIt :: a -> (r -> m (It m r a)) -> It m r a
rollIt = Roll

doneIt :: a -> It m r a
doneIt = Done


needIt :: Monad m => a -> (r -> m (Maybe a)) -> It m r a
needIt a f = i where i = Roll a (fmap (maybe i pure) . f)


tabulateIt :: Monad m => a -> (r -> a) -> It m r a
tabulateIt a f = rollIt a (pure . pure . f)


-- Elimination

foldIt :: Monad m => (a -> m s) -> (a -> (r -> m s) -> m s) -> (It m r a -> m s)
foldIt p k = go where go = runIt p (\ a -> k a . fmap (>>= go))

runIt :: (a -> m s) -> (a -> (r -> m (It m r a)) -> m s) -> (It m r a -> m s)
runIt p k = \case
  Done a   -> p a
  Roll a r -> k a r


evalIt :: Monad m => It m (Maybe r) a -> m a
evalIt = \case
  Done a   -> pure a
  Roll _ k -> evalIt =<< k Nothing


headIt :: It m r a -> a
headIt = \case
  Done a   -> a
  Roll a _ -> a


indexIt :: Monad m => It m r a -> r -> m a
indexIt = \case
  Done a   -> const (pure a)
  Roll _ k -> fmap headIt . k


-- Computation

simplifyIt :: Monad m => It m r a -> r -> m (It m r a)
simplifyIt i r = case i of
  Done{}   -> pure i
  Roll _ k -> k r


-- Parsing


getLineIt :: Monad m => It m (Maybe Char) String
getLineIt = loop id
  where
  loop = rollIt "" . fmap pure . \ acc -> \case
    Just c | c /= '\n' -> loop (acc . (c:))
    _                  -> pure (acc [])

getLinesIt :: Monad m => It m (Maybe Char) [String]
getLinesIt = loop id
  where
  loop acc = getLineIt >>= \case
    "" -> pure (acc [])
    l  -> loop (acc . (l:))


-- Enumerators

newtype Enumerator i m o = Enumerator { getEnumerator :: It m i o -> m (It m i o) }


enumerateList :: Monad m => [r] -> Enumerator (Maybe r) m a
enumerateList = Enumerator . go
  where
  go []     = pure
  go (c:cs) = \ i -> runIt (const (pure i)) (\ _ k -> go cs =<< k (Just c)) i


-- Enumeratees

newtype Enumeratee i o m a = Enumeratee { getEnumeratee :: It m i a -> It m o (It m i a) }

take :: Monad m => Int -> Enumeratee i i m o
take = Enumeratee . go
  where
  go n
    | n <= 0    = pure
    | otherwise = \case
      i@Done{} -> pure i
      Roll a r -> rollIt (pure a) (fmap (go (n - 1)) . r)
