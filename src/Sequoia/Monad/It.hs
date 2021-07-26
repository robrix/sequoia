module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Input
, Input(..)
, input
  -- * Construction
, doneIt
, rollIt
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
, enumList
, enumFile
, enumHandle
  -- * Enumeratees
, Enumeratee
, take
) where

import Control.Applicative (Alternative(..))
import Control.Effect.Lift
import Control.Monad ((<=<))
import Foreign.C.String
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Prelude hiding (any, take)
import System.IO

-- Iteratees

-- | Iteratees, based loosely on the one in @trifecta@.
data It r m a
  = Done a
  | Roll (Input r -> m (It r m a))

instance Functor m => Functor (It r m) where
  fmap f = go where go = runIt (doneIt . f) (rollIt . (fmap go .))

instance Functor m => Applicative (It r m) where
  pure = Done
  f <*> a = runIt (<$> a) (rollIt . (fmap (<*> a) .)) f

instance Monad m => Monad (It r m) where
  m >>= f = go m
    where
    go = runIt f (\ k -> rollIt (\ r -> runIt ((`simplifyIt` r) . f) (pure . rollIt . (pure . go <=<)) =<< k r))


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

doneIt :: a -> It r m a
doneIt = Done

rollIt :: (Input r -> m (It r m a)) -> It r m a
rollIt = Roll


needIt :: Applicative m =>  (r -> m (Maybe a)) -> It r m a
needIt f = i where i = rollIt (input (pure i) (fmap (maybe i doneIt) . f))


toList :: Applicative m => It a m [a]
toList = ($ []) <$> go id
  where
  go as = i where i = rollIt (pure . input (pure as) (\ a -> go (as . (a:))))


-- Elimination

foldIt :: Monad m => (a -> m s) -> ((Input r -> m s) -> m s) -> (It r m a -> m s)
foldIt p k = go where go = runIt p (k . fmap (>>= go))

runIt :: (a -> s) -> ((Input r -> m (It r m a)) -> s) -> (It r m a -> s)
runIt p k = \case
  Done a -> p a
  Roll r -> k r


evalIt :: Monad m => It r m a -> m a
evalIt = runIt pure (evalIt <=< ($ End))


-- Computation

simplifyIt :: Applicative m => It r m a -> Input r -> m (It r m a)
simplifyIt i r = runIt (const (pure i)) ($ r) i


-- Parsing

getLineIt :: Applicative m => It Char m String
getLineIt = loop id
  where
  loop = rollIt . fmap pure . \ acc -> \case
    Input c | c /= '\n' -> loop (acc . (c:))
    _                   -> doneIt (acc [])

getLinesIt :: Monad m => It Char m [String]
getLinesIt = loop id
  where
  loop acc = getLineIt >>= \case
    "" -> pure (acc [])
    l  -> loop (acc . (l:))


-- Enumerators

type Enumerator i m o = It i m o -> m (It i m o)

enumList :: Monad m => [r] -> Enumerator r m a
enumList = go
  where
  go []     = pure
  go (c:cs) = \ i -> runIt (const (pure i)) (go cs <=< ($ Input c)) i

enumFile :: Has (Lift IO) sig m => FilePath -> Enumerator Char m a
enumFile path = withFile' path ReadMode . flip enumHandle

enumHandle :: Has (Lift IO) sig m => Handle -> Enumerator Char m a
enumHandle handle i = runIt (const (pure i)) (allocaBytes' size . loop) i
  where
  size = 4096
  loop k p = do
    n <- sendIO (hGetBuf handle p size)
    sendIO (peekCAStringLen (p, n)) >>= \case
      c:cs -> k (Input c) >>= enumList cs
      ""   -> k End

allocaBytes' :: Has (Lift IO) sig m => Int -> (Ptr a -> m b) -> m b
allocaBytes' n b = liftWith (\ hdl ctx -> allocaBytes n (\ p -> hdl (b p <$ ctx)))

withFile' :: Has (Lift IO) sig m => FilePath -> IOMode -> (Handle -> m r) -> m r
withFile' path mode body = liftWith (\ hdl ctx -> withFile path mode (\ h -> hdl (body h <$ ctx)))


-- Enumeratees

type Enumeratee i o m a = It i m a -> It o m (It i m a)

take :: Monad m => Int -> Enumeratee i i m o
take = go
  where
  go n
    | n <= 0    = pure
    | otherwise = \ i -> runIt (const (pure i)) (rollIt . (fmap (go (n - 1)) .)) i
