module Sequoia.Functor.Source
( -- * Sources
  _Src
, Src(..)
  -- * Computation
, mapSrcK
, mapSrcV
  -- * Optics
, _SrcExp
) where

import Data.Profunctor
import Sequoia.Continuation
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Optic.Getter
import Sequoia.Optic.Iso
import Sequoia.Optic.Review
import Sequoia.Optic.Setter
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Exponential
import Sequoia.Value

-- Sources

_Src :: Iso (Src e r b) (Src e' r' b') (K r b -> C e r) (K r' b' -> C e' r')
_Src = runSrc <-> Src

newtype Src e r b = Src { runSrc :: K r b -> C e r }

instance Functor (Src e r) where
  fmap f = over _Src (. contramap f)

instance Applicative (Src e r) where
  pure = Src . fmap res . flip runK
  Src f <*> Src a = Src (\ k -> cont (\ _K -> f (_K (\ f -> a (inK (exK k . f))))))

instance Monad (Src e r) where
  Src m >>= f = Src (\ k -> cont (\ _K -> m (_K ((`runSrc` k) . f))))

instance Env1 Src where
  env1 f = Src (\ k -> env ((`runSrc` k) . f))

instance Res1 Src where
  res1 = Src . const . res
  liftRes1 f = Src (\ k -> liftRes (\ run -> runSrc (f (run . (`runSrc` k))) k))


-- Computation

mapSrcK :: (forall x . K r x <-> K r' x) -> (Src e r b -> Src e r' b)
mapSrcK b = over _Src (dimap (review b) (mapCK (view b)))

mapSrcV :: (forall x . V e x -> V e' x) -> (Src e r b -> Src e' r b)
mapSrcV f = over _Src (fmap (mapCV f))


-- Optics

_SrcExp :: (Exponential f, Exponential f') => Iso (Src e r b) (Src e' r' b') (f e r e b) (f' e' r' e' b')
_SrcExp = _Src.from (_Exponential.constant idV)
