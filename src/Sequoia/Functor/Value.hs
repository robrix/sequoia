{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Functor.Value
( -- * Values
  Value
, Representable(..)
  -- * Construction
, inV0
, inV
, idV
  -- * Elimination
, (∘)
  -- * Coercion
, _V
  -- * Computation
, (>∘∘<)
, (>∘∘∘<)
, (<∘∘>)
  -- * Ambient environment
, Env(..)
, val
, Env1(..)
, val1
, Env2(..)
, val2
  -- * Value functor
, V(..)
) where

import           Control.Applicative (liftA2)
import           Control.Monad (join)
import           Data.Distributive
import           Data.Functor.Identity
import           Data.Functor.Rep
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve
import           Sequoia.Conjunction
import           Sequoia.Disjunction
import           Sequoia.Optic.Iso

-- Values

class Representable v => Value v

instance Value (V s)


-- Construction

inV0 :: Representable v => a -> v a
inV0 = inV . const

inV :: Representable v => (Rep v -> a) -> v a
inV = tabulate

inV2 :: Representable v => ((Rep v -> a) -> (Rep v -> b) -> (Rep v -> c)) -> (v a -> v b -> v c)
inV2 f a b = inV (exV a `f` exV b)

idV :: Representable v => v (Rep v)
idV = inV id


-- Elimination

exV :: Representable v => v a -> (Rep v -> a)
exV = index


(∘) :: Representable v => Rep v -> v a -> a
(∘) = flip exV

infixr 8 ∘


-- Coercion

_V :: (Representable v, Representable v') => Iso (v a) (v' a') (Rep v -> a) (Rep v' -> a')
_V = exV <-> inV


-- Computation

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

instance Env (Forget r) where
  env = Forget . (runForget =<<)

val :: (Env c, Representable v) => (a -> c (Rep v) r) -> (v a -> c (Rep v) r)
val f v = env (f . exV v)


class Env1 c where
  env1 :: (e -> c e r a) -> c e r a

val1 :: (Env1 c, Representable v) => (a -> c (Rep v) r a) -> (v a -> c (Rep v) r a)
val1 f v = env1 (f . exV v)


class Env2 c where
  env2 :: (e -> c e r a b) -> c e r a b

val2 :: (Env2 c, Representable v) => (a -> c (Rep v) r i o) -> (v a -> c (Rep v) r i o)
val2 f v = env2 (f . exV v)


-- Value functor

newtype V s a = V { runV :: s -> a }
  deriving (Applicative, Choice, Closed, Cochoice, Costrong, Functor, Monad, Monoid, Profunctor, Representable, Pro.Representable, Semigroup, Strong)

instance Distributive (V s) where
  distribute = distributeRep
  collect = collectRep

instance Sieve V Identity where
  sieve = sieve . runV

instance Cosieve V Identity where
  cosieve = cosieve . runV
