module Sequoia.Value
( -- * Values
  Value
, VRep
, VFn
, _V
, inV
, exV
) where

import Data.Functor.Rep
import Sequoia.Bijection

class Representable v => Value v

type VRep v = Rep v
type VFn v a = VRep v -> a


_V :: (Value v, Value v') => Optic Iso (VFn v a) (VFn v' a') (v a) (v' a')
_V = inV <-> exV

inV :: Value v => VFn v a -> v a
inV = tabulate

exV :: Value v => v a -> VFn v a
exV = index
