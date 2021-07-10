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

import Control.Applicative (liftA2)
import Control.Comonad
import Data.Functor.Adjunction
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

appEnv :: (Value v, Value g) => Env g v a -> VRep g -> VRep v -> a
appEnv f = exV . exV (runEnv f)

newtype Env g v a = Env { runEnv :: g (v a) }
  deriving (Functor)

instance Adjunction v g => Applicative (Env g v) where
  pure = Env . unit
  liftA2 f (Env a) b = Env (rightAdjunct (runEnv . (<$> b) . f) <$> a)
  Env f <*> a = Env (rightAdjunct (runEnv . (<$> a)) <$> f)

instance Adjunction v g => Monad (Env g v) where
  (>>=) = flip (\ f -> Env . fmap (rightAdjunct (runEnv . f)) . runEnv)

instance Adjunction g v => Comonad (Env g v) where
  extract = counit . runEnv
  extend f = Env . fmap (leftAdjunct (f . Env)) . runEnv
  duplicate = Env . fmap (leftAdjunct Env) . runEnv
