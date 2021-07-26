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
, repeatIt
  -- * Elimination
, foldIt
, runIt
, evalIt
  -- * Computation
, feedIt
  -- * Parsing
, Line(..)
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

import           Control.Applicative (Alternative(..))
import qualified Control.Category as Cat
import           Control.Effect.Lift
import           Control.Monad (guard)
import           Data.Profunctor
import           Foreign.C.String
import           Foreign.Marshal.Alloc
import           Foreign.Ptr
import           Prelude hiding (any, take)
import           System.IO

-- Iteratees

-- | Iteratees, based loosely on the one in @trifecta@.
newtype It r a = It { getIt :: forall s . (a -> s) -> ((Input r -> It r a) -> s) -> s }

instance Cat.Category It where
  id = rollIt (input Cat.id doneIt)
  f . g = rollIt (\ a -> foldIt (\ b -> foldIt pure ($ Input b) f) ($ a) g)

instance Profunctor It where
  dimap f g = go where go = runIt (doneIt . g) (\ k -> rollIt (go . k . fmap f))

instance Functor (It r) where
  fmap f = go where go = runIt (doneIt . f) (rollIt . (go .))

instance Applicative (It r) where
  pure = doneIt
  f <*> a = runIt (<$> a) (rollIt . ((<*> a) .)) f

instance Monad (It r) where
  m >>= f = foldIt f rollIt m


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

doneIt :: a -> It r a
doneIt a = It (\ f _ -> f a)

rollIt :: (Input r -> It r a) -> It r a
rollIt k = It (\ _ f -> f k)


needIt :: (r -> Maybe a) -> It r a
needIt f = i where i = rollIt (input i (maybe i doneIt . f))


toList :: It a [a]
toList = ($ []) <$> go id
  where
  go as = i where i = rollIt (input (pure as) (\ a -> go (as . (a:))))

repeatIt :: (b -> Maybe c) -> It a b -> It a [c]
repeatIt rel i = loop id
  where
  loop acc = i >>= maybe (pure (acc [])) (loop . fmap acc . (:)) . rel


-- Elimination

foldIt :: (a -> s) -> ((Input r -> s) -> s) -> (It r a -> s)
foldIt p k = go where go = runIt p (k . fmap go)

runIt :: (a -> s) -> ((Input r -> It r a) -> s) -> (It r a -> s)
runIt p k (It i) = i p k


evalIt :: Monad m => It r a -> m a
evalIt = runIt pure (evalIt . ($ End))


-- Computation

feedIt :: It r a -> Input r -> It r a
feedIt i r = runIt (const i) ($ r) i


-- Parsing

data Line = Line { lineContents :: String, lineEnding :: Maybe Newline }
  deriving (Eq, Ord, Show)

nullLine :: Line -> Bool
nullLine = (&&) <$> null . lineContents <*> null . lineEnding

getLineIt :: It Char Line
getLineIt = loop id Nothing
  where
  loop acc prev = rollIt $ \case
    Input '\n' -> doneIt (Line (acc []) (Just (if prev == Just '\r' then CRLF else LF)))
    Input c    -> loop (acc . (c:)) (Just c)
    End        -> doneIt (Line (acc []) Nothing)

getLinesIt :: It Char [Line]
getLinesIt = repeatIt (guarding (not . nullLine)) getLineIt

guarding :: Alternative m => (a -> Bool) -> (a -> m a)
guarding p a = a <$ guard (p a)


-- Enumerators

type Enumerator i m o = It i o -> m (It i o)

enumList :: Monad m => [r] -> Enumerator r m a
enumList = fmap pure . go
  where
  go []     = id
  go (c:cs) = \ i -> runIt (const i) (go cs . ($ Input c)) i

enumFile :: Has (Lift IO) sig m => FilePath -> Enumerator Char m a
enumFile path = withFile' path ReadMode . flip enumHandle

enumHandle :: Has (Lift IO) sig m => Handle -> Enumerator Char m a
enumHandle handle i = runIt (const (pure i)) (allocaBytes' size . loop) i
  where
  size = 4096
  loop k p = do
    n <- sendIO (hGetBuf handle p size)
    sendIO (peekCAStringLen (p, n)) >>= \case
      c:cs -> enumList cs (k (Input c))
      ""   -> pure (k End)

allocaBytes' :: Has (Lift IO) sig m => Int -> (Ptr a -> m b) -> m b
allocaBytes' n b = liftWith (\ hdl ctx -> allocaBytes n (\ p -> hdl (b p <$ ctx)))

withFile' :: Has (Lift IO) sig m => FilePath -> IOMode -> (Handle -> m r) -> m r
withFile' path mode body = liftWith (\ hdl ctx -> withFile path mode (\ h -> hdl (body h <$ ctx)))


-- Enumeratees

type Enumeratee i o a = It i a -> It o (It i a)

take :: Int -> Enumeratee i i o
take = go
  where
  go n
    | n <= 0    = pure
    | otherwise = \ i -> runIt (const (pure i)) (rollIt . (go (n - 1) .)) i
