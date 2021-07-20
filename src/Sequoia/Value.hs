{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Value
( -- * Values
  Value
, Representable(..)
  -- * Construction
, inV0
, inV
, inV1
, inV2
, idV
  -- * Elimination
, exV
, exV1
, exV2
, (∘)
  -- * Coercion
, _V
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
, Env2(..)
, val2
) where

import Control.Applicative (liftA2)
import Control.Monad (join)
import Data.Functor.Rep
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Functor.V
import Sequoia.Optic.Iso
import Sequoia.Optic.Setter

-- Values

class Representable v => Value v

instance Value (V s)


-- Construction

inV0 :: Representable v => a -> v a
inV0 = inV . const

inV :: Representable v => (Rep v -> a) -> v a
inV = tabulate

inV1 :: Representable v => ((Rep v -> a) -> (Rep v -> b)) -> (v a -> v b)
inV1 = over _V

inV2 :: Representable v => ((Rep v -> a) -> (Rep v -> b) -> (Rep v -> c)) -> (v a -> v b -> v c)
inV2 f a b = inV (exV a `f` exV b)

idV :: Representable v => v (Rep v)
idV = inV id


-- Elimination

exV :: Representable v => v a -> (Rep v -> a)
exV = index

exV1 :: Representable v => (v a -> v b) -> ((Rep v -> a) -> (Rep v -> b))
exV1 = under _V

exV2 :: Representable v => (v a -> v b -> v c) -> ((Rep v -> a) -> (Rep v -> b) -> (Rep v -> c))
exV2 f a b = exV (inV a `f` inV b)


(∘) :: Representable v => Rep v -> v a -> a
(∘) = flip exV

infixr 8 ∘


-- Coercion

_V :: (Representable v, Representable v') => Iso (v a) (v' a') (Rep v -> a) (Rep v' -> a')
_V = exV <-> inV

coerceVWith :: (Representable v1, Representable v2) => ((Rep v1 -> a) -> (Rep v2 -> b)) -> (v1 a -> v2 b)
coerceVWith = over _V

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
mapVRep f = over _V (. f)


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

class Env c where
  env :: (e -> c e r) -> c e r

instance Env (->) where
  env = join

instance Env V where
  env f = V (runV =<< f)

val :: (Env c, Representable v) => (a -> c (Rep v) r) -> (v a -> c (Rep v) r)
val f v = env (f . exV v)


class Env1 c where
  env1 :: (e -> c e r a) -> c e r a


class Env2 c where
  env2 :: (e -> c e r a b) -> c e r a b

val2 :: (Env2 c, Representable v) => (a -> c (Rep v) r i o) -> (v a -> c (Rep v) r i o)
val2 f v = env2 (f . exV v)
