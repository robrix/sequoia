module Sequoia.Functor.Source.Internal
( _Src
, Src(..)
) where

import Data.Profunctor
import Sequoia.Optic.Iso
import Sequoia.Optic.Setter
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation

_Src :: Iso (Src e r b) (Src e' r' b') (b • r -> e ==> r) (b' • r' -> e' ==> r')
_Src = coerced

newtype Src e r b = Src { exSrcFn :: (b -> r) -> (e -> r) }

instance Functor (Src e r) where
  fmap f = over _Src (. lmap f)

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
