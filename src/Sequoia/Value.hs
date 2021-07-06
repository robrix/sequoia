module Sequoia.Value
( -- * Values
  Value
, VRep
, VFn
, _V
, inV
, inV1
, inV2
, exV
, exV1
, exV2
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
