module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Input
, Input(..)
, input
  -- * Construction
, rollIt
, doneIt
, needIt
, wantIt
, tabulateIt
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
, Enumerator(..)
, enumerateList
, enumerateFile
, enumerateHandle
  -- * Enumeratees
, Enumeratee(..)
, take
) where

import Control.Applicative (Alternative(..))
import Control.Comonad
import Control.Monad ((<=<))
import Data.Functor.Identity
import Data.Profunctor
import Data.Profunctor.Sieve
import Foreign.C.String
import Foreign.Marshal.Alloc
import Prelude hiding (any, take)
import System.IO

-- Iteratees

-- | Iteratees, based loosely on the one in @trifecta@.
data It m r a
  = Done a
  | Roll a (Input r -> m (It m r a))

instance Functor m => Profunctor (It m) where
  dimap f g = go
    where
    go = \case
      Done a   -> Done (g a)
      Roll a r -> Roll (g a) (fmap go . r . fmap f)

instance Functor m => Costrong (It m) where
  unfirst = \case
    Done (b, _)   -> pure b
    Roll (b, d) k -> Roll b (fmap unfirst . k . fmap (,d))
  unsecond = \case
    Done (_, b)   -> pure b
    Roll (d, b) k -> Roll b (fmap unsecond . k . fmap (d,))

instance Comonad m => Cosieve (It m) Identity where
  cosieve = \case
    Done a   -> const a
    Roll _ k -> extract . extract . k . Input . runIdentity

instance Functor m => Functor (It m r) where
  fmap = rmap

instance Functor m => Applicative (It m r) where
  pure = doneIt
  f <*> a = case f of
    Done f   -> f <$> a
    Roll f k -> Roll (headIt (f <$> a)) (fmap (<*> a) . k)

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

rollIt :: a -> (Input r -> m (It m r a)) -> It m r a
rollIt = Roll

doneIt :: a -> It m r a
doneIt = Done


needIt :: Applicative m => a -> (r -> m (Maybe a)) -> It m r a
needIt a f = i where i = Roll a (input (pure i) (fmap (maybe i Done) . f))

wantIt :: Applicative m => a -> (r -> m (Either a a)) -> It m r a
wantIt a f = Roll a k where k = input (pure (pure a)) (fmap (either Done (`Roll` k)) . f)


tabulateIt :: Applicative m => a -> (Input r -> a) -> It m r a
tabulateIt a f = rollIt a (pure . Done . f)


toList :: Applicative m => It m a [a]
toList = ($ []) <$> go id
  where
  go as = i where i = Roll as (input (pure i) (\ a -> pure (go (as . (a:)))))


-- Elimination

foldIt :: Monad m => (a -> m s) -> (a -> (Input r -> m s) -> m s) -> (It m r a -> m s)
foldIt p k = go where go = runIt p (\ a -> k a . fmap (>>= go))

runIt :: (a -> m s) -> (a -> (Input r -> m (It m r a)) -> m s) -> (It m r a -> m s)
runIt p k = \case
  Done a   -> p a
  Roll a r -> k a r


evalIt :: Monad m => It m r a -> m a
evalIt = \case
  Done a   -> pure a
  Roll _ k -> k End >>= \case
    Done a   -> pure a
    Roll a _ -> pure a


headIt :: It m r a -> a
headIt = \case
  Done a   -> a
  Roll a _ -> a


indexIt :: Applicative m => It m r a -> Input r -> m a
indexIt = \case
  Done a   -> const (pure a)
  Roll _ k -> fmap headIt . k


-- Computation

simplifyIt :: Applicative m => It m r a -> Input r -> m (It m r a)
simplifyIt i r = case i of
  Done{}   -> pure i
  Roll _ k -> k r


-- Parsing

getLineIt :: Applicative m => It m Char String
getLineIt = loop id
  where
  loop = rollIt "" . fmap pure . \ acc -> \case
    Input c | c /= '\n' -> loop (acc . (c:))
    _                   -> Done (acc [])

getLinesIt :: Monad m => It m Char [String]
getLinesIt = loop id
  where
  loop acc = getLineIt >>= \case
    "" -> pure (acc [])
    l  -> loop (acc . (l:))


-- Enumerators

newtype Enumerator i m o = Enumerator { getEnumerator :: It m i o -> m (It m i o) }


enumerateList :: Monad m => [r] -> Enumerator r m a
enumerateList = Enumerator . go
  where
  go []     = pure
  go (c:cs) = \ i -> runIt (const (pure i)) (\ _ k -> go cs =<< k (Input c)) i

enumerateFile :: FilePath -> Enumerator Char IO a
enumerateFile path = Enumerator (withFile path ReadMode . flip (getEnumerator . enumerateHandle))

enumerateHandle :: Handle -> Enumerator Char IO a
enumerateHandle handle = Enumerator $ \case
  i@Done{} -> pure i
  Roll _ k -> allocaBytes size (loop k)
  where
  size = 4096
  loop k p = do
    n <- hGetBuf handle p size
    peekCAStringLen (p, n) >>= \case
      c:cs -> k (Input c) >>= getEnumerator (enumerateList cs)
      ""   -> k End


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
