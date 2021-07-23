module Sequoia.Functor.Source.Internal
( Src(..)
) where

import Data.Profunctor

newtype Src e r b = Src { exSrcFn :: (b -> r) -> (e -> r) }

instance Functor (Src e r) where
  fmap f = Src . (. lmap f) . exSrcFn

instance Applicative (Src e r) where
  pure = Src . fmap const . flip ($)
  Src f <*> Src a = Src (\ k e -> f (\ f -> a (k . f) e) e)

instance Monad (Src e r) where
  Src m >>= f = Src (\ k e -> m (\ a -> exSrcFn (f a) k e) e)
