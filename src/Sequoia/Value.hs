module Sequoia.Value
( Value
, VRep
) where

import Data.Functor.Rep

class Representable v => Value v

type VRep v = Rep v
