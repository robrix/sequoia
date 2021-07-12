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
, inV1'
, inV2
, exV
, exV1
, exV2
, (∘)
  -- * Computation
, liftV2
, (>∘∘<)
, (<∘∘>)
  -- * Env monad
, Env(..)
) where

import Control.Applicative (liftA2)
import Data.Functor.Rep
import Sequoia.Bijection
import Sequoia.Conjunction
import Sequoia.Disjunction
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

inV1' :: Representable v => (v a -> (VRep v -> b)) -> (v a -> v b)
inV1' = fmap inV

inV2 :: Representable v => ((VRep v -> a) -> (VRep v -> b) -> (VRep v -> c)) -> (v a -> v b -> v c)
inV2 = dimap2 exV exV inV

exV :: Representable v => v a -> (VRep v -> a)
exV = index

exV1 :: Representable v => (v a -> v b) -> ((VRep v -> a) -> (VRep v -> b))
exV1 = over _V

exV2 :: Representable v => (v a -> v b -> v c) -> ((VRep v -> a) -> (VRep v -> b) -> (VRep v -> c))
exV2 = dimap2 inV inV exV


(∘) :: Representable v => VRep v -> v a -> a
(∘) = flip exV

infixr 8 ∘


-- Computation

liftV2 :: Representable v => (a -> b -> c) -> v a -> v b -> v c
liftV2 f = inV2 (liftA2 f)


(>∘∘<) :: (Conj c, Representable v) => v a -> v b -> v (a `c` b)
(>∘∘<) = inV2 (>--<)

infix 3 >∘∘<


(<∘∘>) :: (Disj d, Representable v) => (v a -> v r) -> (v b -> v r) -> (v (a `d` b) -> v r)
(l <∘∘> r) ab = inV (\ e -> e ∘ (l . inV0 <--> r . inV0) (e ∘ ab))

infix 3 <∘∘>


-- Env monad

newtype Env v a = Env { runEnv :: v a }
  deriving (Functor)

instance Representable v => Applicative (Env v) where
  pure a = Env (pureRep a)

  Env f <*> Env a = Env (apRep f a)

instance Representable v => Monad (Env v) where
  Env m >>= f = Env (bindRep m (runEnv . f))
