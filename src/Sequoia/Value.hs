module Sequoia.Value
( -- * Values
  Value
, VRep
, VFn
, inV
, exV
) where

import Data.Functor.Rep

class Representable v => Value v

type VRep v = Rep v
type VFn v a = VRep v -> a


inV :: Value v => VFn v a -> v a
inV = tabulate

exV :: Value v => v a -> VFn v a
exV = index
