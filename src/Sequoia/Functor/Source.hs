module Sequoia.Functor.Source
( -- * Sources
  Src(..)
) where

import Sequoia.Continuation
import Sequoia.Functor.K
import Sequoia.Profunctor.Context
import Sequoia.Value

-- Sources

newtype Src e r b = Src { runSrc :: K r b -> C e r }

instance Functor (Src e r) where
  fmap f = Src . (. contramap f) . runSrc

instance Applicative (Src e r) where
  pure = Src . fmap res . flip runK
  Src f <*> Src a = Src (\ k -> cont (\ _K -> f (_K (\ f -> a (inK (exK k . f))))))

instance Env1 Src where
  env1 f = Src (\ k -> env ((`runSrc` k) . f))

instance Res1 Src where
  res1 = Src . const . res
  liftRes1 f = Src (\ k -> liftRes (\ run -> runSrc (f (run . (`runSrc` k))) k))
