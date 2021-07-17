{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Value
( -- * Values
  Value
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
, idV
  -- * Coercion
, coerceVWith
, coerceV
, coerceV1
, coerceV2
  -- * Computation
, liftV2
, mapVRep
, (>∘∘<)
, (>∘∘∘<)
, (<∘∘>)
  -- * Ambient environment
, Env(..)
, val
, Env1(..)
, LocalEnv(..)
, LocalEnv2(..)
) where

import Control.Applicative (liftA2)
import Data.Functor.Rep
import Data.Profunctor
import Sequoia.Bijection
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Functor.V

class Representable v => Value v

instance Value (V s)


_V :: (Representable v, Representable v') => Optic Iso (v a) (v' a') (Rep v -> a) (Rep v' -> a')
_V = exV <-> inV

inV0 :: Representable v => a -> v a
inV0 = inV . const

inV :: Representable v => (Rep v -> a) -> v a
inV = tabulate

inV1 :: Representable v => ((Rep v -> a) -> (Rep v -> b)) -> (v a -> v b)
inV1 = under _V

inV1' :: Representable v => (v a -> (Rep v -> b)) -> (v a -> v b)
inV1' = fmap inV

inV2 :: Representable v => ((Rep v -> a) -> (Rep v -> b) -> (Rep v -> c)) -> (v a -> v b -> v c)
inV2 = dimap2 exV exV inV

exV :: Representable v => v a -> (Rep v -> a)
exV = index

exV1 :: Representable v => (v a -> v b) -> ((Rep v -> a) -> (Rep v -> b))
exV1 = over _V

exV2 :: Representable v => (v a -> v b -> v c) -> ((Rep v -> a) -> (Rep v -> b) -> (Rep v -> c))
exV2 = dimap2 inV inV exV


(∘) :: Representable v => Rep v -> v a -> a
(∘) = flip exV

infixr 8 ∘


idV :: Representable v => v (Rep v)
idV = inV id


-- Coercion

coerceVWith :: (Representable v1, Representable v2) => ((Rep v1 -> a) -> (Rep v2 -> b)) -> (v1 a -> v2 b)
coerceVWith = under _V

coerceV :: (Representable v1, Representable v2, Rep v1 ~ Rep v2) => (v1 a -> v2 a)
coerceV = inV . exV

coerceV1 :: (Representable v1, Representable v2, Rep v1 ~ Rep v2) => (v1 a -> v1 b) -> (v2 a -> v2 b)
coerceV1 = inV1 . exV1

coerceV2 :: (Representable v1, Representable v2, Rep v1 ~ Rep v2) => (v1 a -> v1 b -> v1 c) -> (v2 a -> v2 b -> v2 c)
coerceV2 = inV2 . exV2


-- Computation

liftV2 :: Representable v => (a -> b -> c) -> v a -> v b -> v c
liftV2 f = inV2 (liftA2 f)

mapVRep :: (Representable v, Representable v') => (Rep v' -> Rep v) -> v a -> v' a
mapVRep f = under _V (. f)


(>∘∘<) :: (Conj d, Representable v) => v b -> v c -> v (b `d` c)
(>∘∘<) = inV2 (>---<)

infix 3 >∘∘<

(>∘∘∘<) :: (Conj d, Representable v) => (a -> v b) -> (a -> v c) -> (a -> v (b `d` c))
(>∘∘∘<) = liftA2 (>∘∘<)

infix 3 >∘∘∘<


(<∘∘>) :: (Disj d, Representable v) => (v a -> r) -> (v b -> r) -> (v (a `d` b) -> Rep v -> r)
(l <∘∘> r) ab = (l <--> r) . bitraverseDisjV ab

infix 3 <∘∘>

bitraverseDisjV :: (Disj d, Representable v) => v (a `d` b) -> Rep v -> v a `d` v b
bitraverseDisjV d e = bimapDisj inV0 inV0 (e ∘ d)


-- Ambient environment

class Env e c | c -> e where
  env :: (e -> c) -> c

instance Env e (V e a) where
  env f = V (runV =<< f)

val :: (Env (Rep v) c, Representable v) => (a -> c) -> (v a -> c)
val f v = env (f . exV v)


class Env1 e c | c -> e where
  env1 :: (e -> c x) -> c x

instance Env1 e (V e) where
  env1 = env


class LocalEnv c where
  localEnv :: (e -> e') -> c e' r -> c e r

instance LocalEnv V where
  localEnv = lmap


class LocalEnv2 c where
  localEnv2 :: (e -> e') -> c e' r s t -> c e r s t
