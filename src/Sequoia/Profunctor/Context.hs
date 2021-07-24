{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Context
( -- * Context & control profunctor
  _C
, type (==>)(..)
  -- * Construction
, ckv
, (↓↑)
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
, MonadEnv(..)
, val
  -- * Ambient control
, MonadRes(..)
, cont
, (••)
, (•∘)
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
  deriving (Applicative, Arrow, ArrowApply, ArrowChoice, ArrowLoop, Cat.Category, Choice, Closed, Cochoice, Costrong, Functor, Mapping, Monad, MonadEnv e, Profunctor, Co.Representable, Strong, Traversing)

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


-- Construction

ckv :: b • r -> (a -> b) -> e ∘ a -> e ==> r
ckv k f v = C ((k •) . f . (v ∘))

(↓↑) :: a • r -> e ∘ a -> e ==> r
k ↓↑ v = C ((k •) . (v ∘))

infix 9 ↓↑


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

class Monad m => MonadEnv e m | m -> e where
  {-# MINIMAL askEnv | env #-}

  askEnv :: m e
  askEnv = env pure

  env :: (e -> m a) -> m a
  env k = askEnv >>= k

instance MonadEnv e ((->) e) where
  env = join

deriving instance MonadEnv e ((∘) e)
deriving instance MonadEnv e (Recall e a)

instance MonadEnv e (Src e r) where
  env f = Src (\ k -> env ((`runSrcFn` k) . f))

val :: MonadEnv e m => (a -> m b) -> (e ∘ a -> m b)
val f v = env (f . (v ∘))


-- Ambient control

class MonadRes r m | m -> r where
  res :: r -> m r
  liftRes :: ((m a -> r) -> m a) -> m a

instance MonadRes r (Src e r) where
  res = Src . const . pure
  liftRes f = Src (\ k -> env (\ e -> runSrcFn (f (($ e) . (`runSrcFn` k))) k))

cont :: MonadRes r m => (((a -> m a) -> a • r) -> m a) -> m a
cont f = liftRes (\ run -> f (K . (run .)))


(••) :: MonadRes r m => a • r -> a -> m r
k •• v = res (k • v)

infix 7 ••


(•∘) :: (MonadEnv e m, MonadRes r m) => a • r -> e ∘ a -> m r
k •∘ v = env (\ e -> res (k • v ∘ e))

infix 8 •∘
