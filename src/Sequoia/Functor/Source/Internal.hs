module Sequoia.Functor.Source.Internal
( Src(..)
) where

import Data.Profunctor
import Sequoia.Profunctor.Context

newtype Src e r b = Src { exSrcFn :: (b -> r) -> (e -> r) }

instance Functor (Src e r) where
  fmap f = Src . (. lmap f) . exSrcFn

instance Applicative (Src e r) where
  pure = Src . fmap res . flip ($)
  Src f <*> Src a = Src (\ k -> env (\ e -> f (\ f -> a (k . f) e)))

instance Monad (Src e r) where
  Src m >>= f = Src (\ k -> env (\ e -> m (\ a -> exSrcFn (f a) k e)))

instance Env e (Src e r b) where
  env f = Src (\ k -> env ((`exSrcFn` k) . f))

instance Res r (Src e r b) where
  res = Src . const . res
  liftRes f = Src (\ k -> liftRes (\ run -> exSrcFn (f (run . (`exSrcFn` k))) k))
