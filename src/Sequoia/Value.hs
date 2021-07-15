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
  -- * Computation
, liftV2
, mapVRep
, (>∘∘<)
, (<∘∘>)
  -- * Env monad
, Env(..)
  -- * Monadic abstraction
, MonadV(..)
) where

import Control.Applicative (liftA2)
import Data.Functor.Rep
import Sequoia.Bijection
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Functor.V

class Representable v => Value s v | v -> s

instance Value s (V s)


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


-- Computation

liftV2 :: Representable v => (a -> b -> c) -> v a -> v b -> v c
liftV2 f = inV2 (liftA2 f)

mapVRep :: (Representable v, Representable v') => (Rep v' -> Rep v) -> v a -> v' a
mapVRep f = inV . (. f) . exV


(>∘∘<) :: (Conj c, Representable v) => v a -> v b -> v (a `c` b)
(>∘∘<) = inV2 (>--<)

infix 3 >∘∘<


(<∘∘>) :: (Disj d, Representable v) => (v a -> r) -> (v b -> r) -> (v (a `d` b) -> Rep v -> r)
(l <∘∘> r) ab e = (l <--> r) (bitraverseDisjV ab e)

infix 3 <∘∘>

bitraverseDisjV :: (Disj d, Representable v) => v (a `d` b) -> Rep v -> (v a `d` v b)
bitraverseDisjV d e = bimapDisj inV0 inV0 (e ∘ d)


-- Env monad

newtype Env v a = Env { runEnv :: v a }
  deriving (Functor)

instance Representable v => Applicative (Env v) where
  pure a = Env (pureRep a)

  Env f <*> Env a = Env (apRep f a)

instance Representable v => Monad (Env v) where
  Env m >>= f = Env (bindRep m (runEnv . f))


-- Monadic abstraction

class (Representable v, Monad m) => MonadV v m | m -> v where
  {-# MINIMAL (use | env), mapEnv #-}

  use :: v a -> m a
  use v = (∘ v) <$> env

  env :: m (Rep v)
  env = use (inV id)

  mapEnv :: (Rep v -> Rep v) -> m a -> m a

instance Representable v => MonadV v (Env v) where
  use = Env

  env = Env (inV id)

  mapEnv f (Env v) = Env (mapVRep f v)
