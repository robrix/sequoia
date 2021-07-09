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
, (°)
  -- * Env monad
, appEnv
, Env(..)
) where

import Data.Functor.Rep
import Sequoia.Bijection
import Sequoia.Functor.V

class Representable v => Value v

instance Value (V s)

type VRep v = Rep v
type VFn v a = VRep v -> a


_V :: (Value v, Value v') => Optic Iso (v a) (v' a') (VFn v a) (VFn v' a')
_V = exV <-> inV

inV0 :: Value v => a -> v a
inV0 = inV . const

inV :: Value v => VFn v a -> v a
inV = tabulate

inV1 :: Value v => (VFn v a -> VFn v b) -> (v a -> v b)
inV1 = under _V

inV2 :: Value v => (VFn v a -> VFn v b -> VFn v c) -> (v a -> v b -> v c)
inV2 = dimap2 exV exV inV

exV :: Value v => v a -> VFn v a
exV = index

exV1 :: Value v => (v a -> v b) -> (VFn v a -> VFn v b)
exV1 = over _V

exV2 :: Value v => (v a -> v b -> v c) -> (VFn v a -> VFn v b -> VFn v c)
exV2 = dimap2 inV inV exV


(°) :: Value v => VRep v -> v a -> a
(°) = flip exV

infixr 8 °


-- Env monad

appEnv :: Value v => Env v a -> VRep v -> VRep v -> a
appEnv f = exV . exV (runEnv f)

newtype Env v a = Env { runEnv :: v (v a) }

instance Functor v => Functor (Env v) where
  fmap f = Env . fmap (fmap f) . runEnv

instance Value v => Applicative (Env v) where
  pure a = Env (inV (const (inV (const a))))
  f <*> a = Env (inV (\ so -> inV (\ si -> appEnv f so si (appEnv a so si))))

instance Value v => Monad (Env v) where
  m >>= f = Env (inV (\ so -> inV (\ si -> appEnv (f (appEnv m so si)) so si)))
