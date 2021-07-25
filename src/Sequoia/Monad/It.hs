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
, getLineIt
, getLinesIt
  -- * Enumerators
, Enumerator(..)
, enumerateList
  -- * Enumeratees
, Enumeratee(..)
, take
) where

import Control.Applicative (Applicative(liftA2))
import Control.Comonad
import Control.Monad (ap, (<=<))
import Control.Monad.Trans.Class
import Prelude hiding (any, take)

-- Iteratees

-- | Iteratees, based loosely on the one in @trifecta@.
data It r m a
  = Done a
  | Roll a (r -> m (It r m a))

instance Functor m => Functor (It r m) where
  fmap f = \case
    Done a   -> Done (f a)
    Roll a r -> Roll (f a) (fmap (fmap f) . r)

instance Monad m => Applicative (It r m) where
  pure = doneIt
  (<*>) = ap

instance Monad m => Monad (It r m) where
  Done a   >>= f = f a
  Roll a k >>= f = Roll (headIt (f a)) $ \ r -> do
    kr' <- k r
    case kr' of
      Done a'    -> simplifyIt (f a') r
      Roll a' k' -> do
        a'' <- indexIt (f a') r
        pure $ Roll a'' (pure . (f =<<) <=< k')

instance Functor m => Comonad (It r m) where
  extract = headIt

  duplicate = \case
    i@Done{}     -> Done i
    i@(Roll _ k) -> Roll i (fmap duplicate . k)

  extend f = go
    where
    go = \case
      i@Done{}     -> Done (f i)
      i@(Roll _ k) -> Roll (f i) (fmap go . k)


newtype ItM r m a = ItM { getItM :: m (It r m a) }
  deriving (Functor)

instance Monad m => Applicative (ItM r m) where
  pure = ItM . pure . pure
  ItM f <*> ItM a = ItM (liftA2 (<*>) f a)

instance Monad m => Monad (ItM r m) where
  ItM m >>= f = ItM (m >>= go)
    where
    go = \case
      Done a   -> getItM (f a)
      Roll a k -> do
        fa <- getItM (f a)
        pure $ Roll (headIt fa) $ \ r -> do
          kr' <- k r
          case kr' of
            Done a'    -> do
              fa' <- getItM (f a')
              simplifyIt fa' r
            Roll a' k' -> do
              fa' <- getItM (f a')
              a'' <- indexIt fa' r
              pure $ Roll a'' (go <=< k')

instance MonadTrans (ItM r) where
  lift m = ItM (pure <$> m)


-- Construction

rollIt :: a -> (r -> m (It r m a)) -> It r m a
rollIt = Roll

doneIt :: a -> It r m a
doneIt = Done


needIt :: Monad m => a -> (r -> m (Maybe a)) -> It r m a
needIt a f = i where i = Roll a (fmap (maybe i pure) . f)


tabulateIt :: Monad m => a -> (r -> a) -> It r m a
tabulateIt a f = rollIt a (pure . pure . f)


-- Elimination

foldIt :: Monad m => (a -> m s) -> (a -> (r -> m s) -> m s) -> (It r m a -> m s)
foldIt p k = go where go = runIt p (\ a -> k a . fmap (>>= go))

runIt :: (a -> m s) -> (a -> (r -> m (It r m a)) -> m s) -> (It r m a -> m s)
runIt p k = \case
  Done a   -> p a
  Roll a r -> k a r


evalIt :: Monad m => It (Maybe r) m a -> m a
evalIt = \case
  Done a   -> pure a
  Roll _ k -> evalIt =<< k Nothing


headIt :: It r m a -> a
headIt = \case
  Done a   -> a
  Roll a _ -> a


indexIt :: Monad m => It r m a -> r -> m a
indexIt = \case
  Done a   -> const (pure a)
  Roll _ k -> fmap headIt . k


-- Computation

simplifyIt :: Monad m => It r m a -> r -> m (It r m a)
simplifyIt i r = case i of
  Done{}   -> pure i
  Roll _ k -> k r


-- Parsing


getLineIt :: Monad m => It (Maybe Char) m String
getLineIt = loop id
  where
  loop = rollIt "" . fmap pure . \ acc -> \case
    Just c | c /= '\n' -> loop (acc . (c:))
    _                  -> pure (acc [])

getLinesIt :: Monad m => It (Maybe Char) m [String]
getLinesIt = loop id
  where
  loop acc = getLineIt >>= \case
    "" -> pure (acc [])
    l  -> loop (acc . (l:))


-- Enumerators

newtype Enumerator i m o = Enumerator { getEnumerator :: It i m o -> m (It i m o) }


enumerateList :: Monad m => [r] -> Enumerator (Maybe r) m a
enumerateList = Enumerator . go
  where
  go []     = pure
  go (c:cs) = \ i -> runIt (const (pure i)) (\ _ k -> go cs =<< k (Just c)) i


-- Enumeratees

newtype Enumeratee i o m a = Enumeratee { getEnumeratee :: It i m a -> It o m (It i m a) }

take :: Monad m => Int -> Enumeratee i i m o
take = Enumeratee . go
  where
  go n
    | n <= 0    = pure
    | otherwise = \case
      i@Done{} -> pure i
      Roll a r -> rollIt (pure a) (fmap (go (n - 1)) . r)
