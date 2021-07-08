{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Value
( -- * Values
  Value
, VRep
, VFn
, _V
, inV0
, inV
, inV1
, inV2
, exV
, exV1
, exV2
  -- * Env monad
, appEnv
, Env(..)
) where

import Data.Profunctor
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Sequoia.Bijection
import Sequoia.Profunctor.V

class Corepresentable v => Value v

instance Value (V s)

type VRep v = Corep v
type VFn v s a = VRep v s -> a


_V :: (Value v, Value v') => Optic Iso (v s a) (v' s' a') (VFn v s a) (VFn v' s' a')
_V = exV <-> inV

inV0 :: Value v => a -> v s a
inV0 = inV . const

inV :: Value v => VFn v s a -> v s a
inV = cotabulate

inV1 :: Value v => (VFn v s a -> VFn v s b) -> (v s a -> v s b)
inV1 = under _V

inV2 :: Value v => (VFn v s a -> VFn v s b -> VFn v s c) -> (v s a -> v s b -> v s c)
inV2 = dimap2 exV exV inV

exV :: Value v => v s a -> VFn v s a
exV = cosieve

exV1 :: Value v => (v s a -> v s b) -> (VFn v s a -> VFn v s b)
exV1 = over _V

exV2 :: Value v => (v s a -> v s b -> v s c) -> (VFn v s a -> VFn v s b -> VFn v s c)
exV2 = dimap2 inV inV exV


-- Env monad

appEnv :: Value v => Env v a -> VRep v () -> VRep v () -> a
appEnv f = exV . exV (runEnv f)

newtype Env v a = Env { runEnv :: v () (v () a) }

instance Value v => Functor (Env v) where
  fmap f = Env . rmap (rmap f) . runEnv

instance Value v => Applicative (Env v) where
  pure a = Env (inV (const (inV (const a))))
  f <*> a = Env (inV (\ so -> inV (\ si -> appEnv f so si (appEnv a so si))))

instance Value v => Monad (Env v) where
  m >>= f = Env (inV (\ so -> inV (\ si -> appEnv (f (appEnv m so si)) so si)))
