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
import qualified Sequoia.Cons as List
import           Sequoia.Line
import           System.IO hiding (Newline(..))

-- Iteratees

-- | Iteratees, based loosely on the one in @trifecta@.
newtype It i o = It { getIt :: forall s . (o -> s) -> (forall x . (x -> It i o) -> (Maybe i -> x) -> s) -> s }

instance Cat.Category It where
  id = rollIt (maybe Cat.id doneIt)
  f . g = rollIt (\ a -> foldIt (\ b -> foldIt pure ($ Just b) f) ($ a) g)

instance Profunctor It where
  dimap f g = mfoldIt (doneIt . g) ((. (. fmap f)) . mrollIt)

instance Choice It where
  left'  = foldIt (pure . Left)  (\ k -> rollIt (maybe (k Nothing) (either (k . Just) (pure . Right))))
  right' = foldIt (pure . Right) (\ k -> rollIt (maybe (k Nothing) (either (pure . Left) (k . Just))))

instance Functor (It i) where
  fmap f = mfoldIt (doneIt . f) mrollIt

instance Applicative (It i) where
  pure = doneIt
  f <*> a = mfoldIt (<$> a) mrollIt f

instance Monad (It i) where
  m >>= f = mfoldIt f mrollIt m


-- Construction

fromGetIt :: (forall s . (o -> s) -> ((Maybe i -> It i o) -> s) -> s) -> It i o
fromGetIt f = mfromGetIt (\ a k -> f a (k id))

mfromGetIt :: (forall s . (o -> s) -> (forall x . (x -> It i o) -> (Maybe i -> x) -> s) -> s) -> It i o
mfromGetIt = It


doneIt :: o -> It i o
doneIt a = fromGetIt (const . ($ a))

rollIt :: (Maybe i -> It i o) -> It i o
rollIt = mrollIt id

mrollIt :: (x -> It i o) -> (Maybe i -> x) -> It i o
mrollIt k r = mfromGetIt (\ _ f -> f k r)


unfoldIt :: (s -> Either o (Maybe i -> s)) -> (s -> It i o)
unfoldIt coalg = go where go = munfoldIt (fmap (id,) . coalg)

munfoldIt :: (s -> Either o (x -> s, Maybe i -> x)) -> (s -> It i o)
munfoldIt coalg = go where go s = mfromGetIt (\ p k -> either p (uncurry (k . (go .))) (coalg s))


needIt :: (i -> Maybe o) -> It i o
needIt f = i where i = rollIt (maybe i (maybe i doneIt . f))


toList :: It a [a]
toList = List.toList <$> go List.nil
  where
  go as = i where i = rollIt (maybe (pure as) (go . List.snoc as))

repeatIt :: (o -> Maybe o') -> It i o -> It i [o']
repeatIt rel i = loop List.nil
  where
  loop acc = i >>= maybe (pure (List.toList acc)) (loop . List.snoc acc) . rel


-- Elimination

foldIt :: (o -> s) -> ((Maybe i -> s) -> s) -> (It i o -> s)
foldIt p k = go where go = mfoldIt p (mk k)

mfoldIt :: (o -> s) -> (forall x . (x -> s) -> ((Maybe i -> x) -> s)) -> (It i o -> s)
mfoldIt p k = go where go = mrunIt p (k . (go .))

runIt :: (o -> s) -> ((Maybe i -> It i o) -> s) -> (It i o -> s)
runIt p k = mrunIt p (mk k)

mrunIt :: (o -> s) -> (forall x . (x -> It i o) -> (Maybe i -> x) -> s) -> (It i o -> s)
mrunIt p k i = getIt i p k


-- | Promote a continuation to a Mendler-style continuation.
mk :: ((Maybe i -> t) -> s) -> (forall x . (x -> t) -> (Maybe i -> x) -> s)
mk k = (k .) . (.)


evalIt :: Monad m => It i o -> m o
evalIt = foldIt pure ($ Nothing)


-- Computation

feedIt :: It i o -> Maybe i -> It i o
feedIt i r = runIt (const i) ($ r) i


-- Parsing

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
