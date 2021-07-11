{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Value
( -- * Values
  Value
, VRep
, VFn
, Representable(..)
, _V
, inV0
, inV
, inV1
, inV2
, exV
, exV1
, exV2
, (°)
, (∘><∘)
) where

import Data.Functor.Rep
import Sequoia.Bijection
import Sequoia.Conjunction
import Sequoia.Functor.V

class Representable v => Value v

instance Value (V s)

type VRep v = Rep v
type VFn v a = VRep v -> a


_V :: (Representable v, Representable v') => Optic Iso (v a) (v' a') (VFn v a) (VFn v' a')
_V = exV <-> inV

inV0 :: Representable v => a -> v a
inV0 = inV . const

inV :: Representable v => (VRep v -> a) -> v a
inV = tabulate

inV1 :: Representable v => ((VRep v -> a) -> (VRep v -> b)) -> (v a -> v b)
inV1 = under _V

inV2 :: Representable v => ((VRep v -> a) -> (VRep v -> b) -> (VRep v -> c)) -> (v a -> v b -> v c)
inV2 = dimap2 exV exV inV

exV :: Representable v => v a -> (VRep v -> a)
exV = index

exV1 :: Representable v => (v a -> v b) -> ((VRep v -> a) -> (VRep v -> b))
exV1 = over _V

exV2 :: Representable v => (v a -> v b -> v c) -> ((VRep v -> a) -> (VRep v -> b) -> (VRep v -> c))
exV2 = dimap2 inV inV exV


(°) :: Representable v => VRep v -> v a -> a
(°) = flip exV

infixr 8 °


(∘><∘) :: (Conj c, Representable v) => v a -> v b -> v (a `c` b)
(∘><∘) = inV2 (-><-)

infix 3 ∘><∘
