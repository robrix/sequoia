module Sequoia.Value
( -- * Values
  Value
, VRep
, inV
, exV
) where

import Data.Functor.Rep

class Representable v => Value v

type VRep v = Rep v


inV :: Value v => (VRep v -> a) -> v a
inV = tabulate

exV :: Value v => v a -> (VRep v -> a)
exV = index
