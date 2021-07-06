module Sequoia.Value
( -- * Values
  Value
, VRep
, VFn
, _V
, inV
, inV1
, exV
, exV1
) where

import Data.Functor.Rep
import Sequoia.Bijection

class Representable v => Value v

type VRep v = Rep v
type VFn v a = VRep v -> a


_V :: (Value v, Value v') => Optic Iso (v a) (v' a') (VFn v a) (VFn v' a')
_V = exV <-> inV

inV :: Value v => VFn v a -> v a
inV = tabulate

inV1 :: (Value v, Value v') => (VFn v a -> VFn v' a') -> (v a -> v' a')
inV1 = under _V

exV :: Value v => v a -> VFn v a
exV = index

exV1 :: (Value v, Value v') => (v a -> v' a') -> (VFn v a -> VFn v' a')
exV1 = over _V
