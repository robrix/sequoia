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

newtype Src e r b = Src { runSrc :: b • r -> e ==> r }

instance Functor (Src e r) where
  fmap f = over _Src (. lmap f)

instance Applicative (Src e r) where
  pure = Src . fmap res . flip (•)
  Src f <*> Src a = Src (\ k -> cont (\ _K -> f (_K (\ f -> a (K ((k •) . f))))))

instance Monad (Src e r) where
  Src m >>= f = Src (\ k -> cont (\ _K -> m (_K ((`runSrc` k) . f))))

instance Env e (Src e r b) where
  env f = Src (\ k -> env ((`runSrc` k) . f))

instance Res r (Src e r b) where
  res = Src . const . res
  liftRes f = Src (\ k -> liftRes (\ run -> runSrc (f (run . (`runSrc` k))) k))
