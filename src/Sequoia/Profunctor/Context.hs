{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Context
( -- * Context & control profunctor
  _C
, type (==>)(..)
  -- * Elimination
, toK
, toV
  -- * Composition
, (•<<)
, (>>•)
, (∘>>)
, (<<∘)
  -- * Computation
, mapCKV
, mapCK
, mapCV
  -- * Ambient environment
, Env(..)
, val
, MonadEnv(..)
, mval
  -- * Ambient control
, Res(..)
, cont
, (••)
, (•∘)
, MonadRes(..)
, mcont
) where

import Control.Arrow
import Control.Category as Cat (Category)
import Control.Monad (join)
import Data.Coerce (coerce)
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing
import Sequoia.Functor.Source.Internal
import Sequoia.Optic.Iso
import Sequoia.Optic.Setter
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Recall
import Sequoia.Profunctor.Value

-- Context & control profunctor

_C :: Iso (e ==> r) (e' ==> r') (e -> r) (e' -> r')
_C = coerced

newtype e ==> r = C { (<==) :: e -> r }
  deriving (Applicative, Arrow, ArrowApply, ArrowChoice, ArrowLoop, Cat.Category, Choice, Closed, Cochoice, Costrong, Env e, Functor, Mapping, Monad, MonadEnv e, Profunctor, Co.Representable, Res r, Strong, Traversing)

infix 6 ==>
infixl 1 <==

instance Distributive ((==>) e) where
  distribute = distributeRep
  collect = collectRep

instance Sieve (==>) Identity where
  sieve = fmap Identity . (<==)

instance Cosieve (==>) Identity where
  cosieve = lmap runIdentity . (<==)

instance Pro.Representable (==>) where
  type Rep (==>) = Identity
  tabulate = C . fmap runIdentity

instance Pro.Corepresentable (==>) where
  type Corep (==>) = Identity
  cotabulate = C . lmap Identity


-- Elimination

toK :: e ==> r -> e • r
toK = coerce

toV :: e ==> r -> e ∘ r
toV = coerce


-- Composition

(•<<) :: r • s -> e ==> r -> e ==> s
(•<<) = rmap . (•)

(>>•) :: e ==> r -> r • s -> e ==> s
(>>•) = flip (•<<)

infixr 1 •<<, >>•


(∘>>) :: d ∘ e -> e ==> r -> d ==> r
(∘>>) = lmap . (∘)

(<<∘) :: e ==> r -> d ∘ e -> d ==> r
(<<∘) = flip (∘>>)

infixr 1 ∘>>, <<∘


-- Computation

mapCKV :: (forall x . x • r -> x • r') -> (forall x . e ∘ x -> e' ∘ x) -> (e ==> r -> e' ==> r')
mapCKV f g = over _C (under _K f . under _V g)

mapCK :: (forall x . x • r -> x • r') -> (e ==> r -> e ==> r')
mapCK = over _C . under _K

mapCV :: (forall x . e ∘ x -> e' ∘ x) -> (e ==> r -> e' ==> r)
mapCV = over _C . under _V


-- Ambient environment

class Env e c | c -> e where
  env :: (e -> c) -> c

instance Env e (e -> a) where
  env = join

deriving instance Env e (e ∘ r)
deriving instance Env e (Forget r e b)
deriving instance Env e (Recall e a b)

instance Env e (Src e r b) where
  env f = Src (\ k -> env ((`runSrcFn` k) . f))

val :: Env e c => (a -> c) -> (e ∘ a -> c)
val f v = env (f . (v ∘))


class Monad m => MonadEnv e m | m -> e where
  menv :: (e -> m a) -> m a

instance MonadEnv e ((->) e) where
  menv = env

deriving instance MonadEnv e ((∘) e)
deriving instance MonadEnv e (Recall e a)

instance MonadEnv e (Src e r) where
  menv f = Src (\ k -> env ((`runSrcFn` k) . f))

mval :: MonadEnv e m => (a -> m b) -> (e ∘ a -> m b)
mval f v = menv (f . (v ∘))


-- Ambient control

class Res r c | c -> r where
  res :: r -> c
  liftRes :: ((c -> r) -> c) -> c

instance Res r (a -> r) where
  res = pure
  liftRes f = f =<< flip ($)

instance Res r (Src e r b) where
  res = Src . const . res
  liftRes f = Src (\ k -> liftRes (\ run -> runSrcFn (f (run . (`runSrcFn` k))) k))

deriving instance Res r (a • r)
deriving instance Res r (Forget r a b)
deriving instance Res r (Recall e a r)

cont :: Res r c => (((a -> c) -> a • r) -> c) -> c
cont f = liftRes (\ run -> f (K . (run .)))

(••) :: Res r c => a • r -> a -> c
k •• v = res (k • v)

infix 7 ••


(•∘) :: (Env e c, Res r c) => a • r -> e ∘ a -> c
k •∘ v = env (\ e -> res (k • v ∘ e))

infix 8 •∘


class MonadRes r m | m -> r where
  mres :: r -> m ()
  mliftRes :: ((m a -> r) -> m a) -> m a

mcont :: MonadRes r m => (((a -> m a) -> a • r) -> m a) -> m a
mcont f = mliftRes (\ run -> f (K . (run .)))
