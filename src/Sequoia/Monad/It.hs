module Sequoia.Monad.It
( -- * Iteratees
  It(..)
  -- * Construction
, fromGetIt
, mfromGetIt
, doneIt
, rollIt
, mrollIt
, unfoldIt
, munfoldIt
, needIt
, toList
, repeatIt
  -- * Elimination
, foldIt
, mfoldIt
, runIt
, mrunIt
, evalIt
  -- * Computation
, feedIt
  -- * Parsing
, Pos(..)
, Span(..)
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
import qualified Sequoia.List as List
import           Sequoia.Span
import           System.IO

-- Iteratees

-- | Iteratees, based loosely on the one in @trifecta@.
newtype It r a = It { getIt :: forall s . (a -> s) -> (forall x . (x -> It r a) -> (Maybe r -> x) -> s) -> s }

instance Cat.Category It where
  id = rollIt (maybe Cat.id doneIt)
  f . g = rollIt (\ a -> foldIt (\ b -> foldIt pure ($ Just b) f) ($ a) g)

instance Profunctor It where
  dimap f g = go where go = foldIt (doneIt . g) (rollIt . (. fmap f))

instance Choice It where
  left'  = foldIt (pure . Left)  (\ k -> rollIt (maybe (k Nothing) (either (k . Just) (pure . Right))))
  right' = foldIt (pure . Right) (\ k -> rollIt (maybe (k Nothing) (either (pure . Left) (k . Just))))

instance Functor (It r) where
  fmap f = go where go = foldIt (doneIt . f) rollIt

instance Applicative (It r) where
  pure = doneIt
  f <*> a = foldIt (<$> a) rollIt f

instance Monad (It r) where
  m >>= f = foldIt f rollIt m


-- Construction

fromGetIt :: (forall s . (a -> s) -> ((Maybe r -> It r a) -> s) -> s) -> It r a
fromGetIt f = mfromGetIt (\ a k -> f a (k id))

mfromGetIt :: (forall s . (a -> s) -> (forall x . (x -> It r a) -> (Maybe r -> x) -> s) -> s) -> It r a
mfromGetIt = It


doneIt :: a -> It r a
doneIt a = fromGetIt (const . ($ a))

rollIt :: (Maybe r -> It r a) -> It r a
rollIt = mrollIt id

mrollIt :: (x -> It r a) -> (Maybe r -> x) -> It r a
mrollIt k r = mfromGetIt (\ _ f -> f k r)


unfoldIt :: (s -> Either a (Maybe r -> s)) -> (s -> It r a)
unfoldIt coalg = go where go = munfoldIt ((. coalg) . fmap . (.))

munfoldIt :: (forall x . (s -> x) -> (s -> Either a (Maybe r -> x))) -> (s -> It r a)
munfoldIt coalg = go where go = either doneIt rollIt . coalg go


needIt :: (r -> Maybe a) -> It r a
needIt f = i where i = rollIt (maybe i (maybe i doneIt . f))


toList :: It a [a]
toList = List.toList <$> go List.nil
  where
  go as = i where i = rollIt (maybe (pure as) (go . List.snoc as))

repeatIt :: (b -> Maybe c) -> It a b -> It a [c]
repeatIt rel i = loop List.nil
  where
  loop acc = i >>= maybe (pure (List.toList acc)) (loop . List.snoc acc) . rel


-- Elimination

foldIt :: (a -> s) -> ((Maybe r -> s) -> s) -> (It r a -> s)
foldIt p k = go where go = mfoldIt p ((k .) . fmap)

mfoldIt :: (a -> s) -> (forall x . (x -> s) -> ((Maybe r -> x) -> s)) -> (It r a -> s)
mfoldIt p k = go where go = mrunIt p (k . (go .))

runIt :: (a -> s) -> ((Maybe r -> It r a) -> s) -> (It r a -> s)
runIt p k = mrunIt p (fmap k . fmap)

mrunIt :: (a -> s) -> (forall x . (x -> It r a) -> (Maybe r -> x) -> s) -> (It r a -> s)
mrunIt p k i = getIt i p k


evalIt :: Monad m => It r a -> m a
evalIt = foldIt pure ($ Nothing)


-- Computation

feedIt :: It r a -> Maybe r -> It r a
feedIt i r = runIt (const i) ($ r) i


-- Parsing

data Line = Line { lineContents :: List.List Char, lineEnding :: Maybe Newline }
  deriving (Eq, Ord, Show)

nullLine :: Line -> Bool
nullLine = (&&) <$> null . lineContents <*> null . lineEnding

getLineIt :: It Char Line
getLineIt = loop List.nil Nothing
  where
  loop acc prev = rollIt $ \case
    Just '\n' -> doneIt (Line acc (Just (if prev == Just '\r' then CRLF else LF)))
    Just c    -> loop (List.snoc acc c) (Just c)
    Nothing   -> doneIt (Line acc Nothing)

getLinesIt :: It Char [Line]
getLinesIt = repeatIt (guarding (not . nullLine)) getLineIt

guarding :: Alternative m => (a -> Bool) -> (a -> m a)
guarding p a = a <$ guard (p a)


-- Enumerators

type Enumerator i m o = It i o -> m (It i o)

enumList :: Monad m => [r] -> Enumerator r m a
enumList = fmap pure . foldr (\ c cs i -> runIt (const i) (cs . ($ Just c)) i) id

enumFile :: Has (Lift IO) sig m => FilePath -> Enumerator Char m a
enumFile path = withFile' path ReadMode . flip enumHandle

enumHandle :: Has (Lift IO) sig m => Handle -> Enumerator Char m a
enumHandle handle i = runIt (const (pure i)) (allocaBytes' size . loop) i
  where
  size = 4096
  loop k p = do
    n <- sendIO (hGetBuf handle p size)
    sendIO (peekCAStringLen (p, n)) >>= \case
      c:cs -> enumList cs (k (Just c))
      ""   -> pure (k Nothing)

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
