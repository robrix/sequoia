module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Input
, Input(..)
, input
  -- * Construction
, needIt
, toList
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
, Enumerator
, enumerateList
, enumerateFile
, enumerateHandle
  -- * Enumeratees
, Enumeratee
, take
) where

import Control.Applicative (Alternative(..))
import Control.Monad ((<=<))
import Data.Profunctor
import Foreign.C.String
import Foreign.Marshal.Alloc
import Prelude hiding (any, take)
import System.IO

-- Iteratees

-- | Iteratees, based loosely on the one in @trifecta@.
data It m r a
  = Done a
  | Roll (Input r -> m (It m r a))

instance Functor m => Profunctor (It m) where
  dimap f g = go
    where
    go = \case
      Done a -> Done (g a)
      Roll r -> Roll (fmap go . r . fmap f)

instance Functor m => Functor (It m r) where
  fmap = rmap

instance Functor m => Applicative (It m r) where
  pure = Done
  f <*> a = case f of
    Done f -> f <$> a
    Roll k -> Roll (fmap (<*> a) . k)

instance Monad m => Monad (It m r) where
  m >>= f = go m
    where
    go = \case
      Done a   -> f a
      Roll k -> Roll $ \ r -> do
        kr' <- k r
        case kr' of
          Done a' -> simplifyIt (f a') r
          Roll k' -> pure $ Roll (pure . go <=< k')


-- Input

data Input r = End | Input r
  deriving (Functor)

instance Applicative Input where
  pure = Input
  End     <*> _ = End
  Input f <*> a = f <$> a

instance Alternative Input where
  empty = End
  End       <|> b = b
  a@Input{} <|> _ = a

instance Monad Input where
  End     >>= _ = End
  Input a >>= f = f a

instance Semigroup a => Semigroup (Input a) where
  Input a   <> Input b = Input (a <> b)
  a@Input{} <> _       = a
  _         <> b       = b

instance Semigroup a => Monoid (Input a) where
  mempty = End


input :: a -> (r -> a) -> (Input r -> a)
input e i = \case
  End     -> e
  Input r -> i r


-- Construction

needIt :: Applicative m =>  (r -> m (Maybe a)) -> It m r a
needIt f = i where i = Roll (input (pure i) (fmap (maybe i Done) . f))


toList :: Applicative m => It m a [a]
toList = ($ []) <$> go id
  where
  go as = i where i = Roll (input (pure i) (\ a -> pure (go (as . (a:)))))


-- Elimination

foldIt :: Monad m => (a -> m s) -> ((Input r -> m s) -> m s) -> (It m r a -> m s)
foldIt p k = go where go = runIt p (k . fmap (>>= go))

runIt :: (a -> m s) -> ((Input r -> m (It m r a)) -> m s) -> (It m r a -> m s)
runIt p k = \case
  Done a -> p a
  Roll r -> k r


evalIt :: Monad m => It m r a -> m (Maybe a)
evalIt = \case
  Done a -> pure (Just a)
  Roll k -> k End >>= \case
    Done a -> pure (Just a)
    Roll _ -> pure Nothing


-- Computation

simplifyIt :: Applicative m => It m r a -> Input r -> m (It m r a)
simplifyIt i r = case i of
  Done{} -> pure i
  Roll k -> k r


-- Parsing

getLineIt :: Applicative m => It m Char String
getLineIt = loop id
  where
  loop = Roll . fmap pure . \ acc -> \case
    Input c | c /= '\n' -> loop (acc . (c:))
    _                   -> Done (acc [])

getLinesIt :: Monad m => It m Char [String]
getLinesIt = loop id
  where
  loop acc = getLineIt >>= \case
    "" -> pure (acc [])
    l  -> loop (acc . (l:))


-- Enumerators

type Enumerator i m o = It m i o -> m (It m i o)

enumerateList :: Monad m => [r] -> Enumerator r m a
enumerateList = go
  where
  go []     = pure
  go (c:cs) = \ i -> runIt (const (pure i)) (\ k -> go cs =<< k (Input c)) i

enumerateFile :: FilePath -> Enumerator Char IO a
enumerateFile path = withFile path ReadMode . flip enumerateHandle

enumerateHandle :: Handle -> Enumerator Char IO a
enumerateHandle handle = \case
  i@Done{} -> pure i
  Roll k   -> allocaBytes size (loop k)
  where
  size = 4096
  loop k p = do
    n <- hGetBuf handle p size
    peekCAStringLen (p, n) >>= \case
      c:cs -> k (Input c) >>= enumerateList cs
      ""   -> k End


-- Enumeratees

type Enumeratee i o m a = It m i a -> It m o (It m i a)

take :: Monad m => Int -> Enumeratee i i m o
take = go
  where
  go n
    | n <= 0    = pure
    | otherwise = \case
      i@Done{} -> pure i
      Roll r   -> Roll (fmap (go (n - 1)) . r)
