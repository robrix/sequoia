{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Context
( -- * Context & control profunctor
  _C
, C(..)
  -- * Computation
, mapCKV
, mapCK
, mapCV
, (•∘)
) where

import Control.Category as Cat (Category)
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing
import Sequoia.Functor.Continuation
import Sequoia.Optic.Iso
import Sequoia.Optic.Setter
import Sequoia.Profunctor.Value

-- Context & control profunctor

_C :: Iso (C e r) (C e' r') (e -> r) (e' -> r')
_C = runC <-> C

newtype C e r = C { runC :: e -> r }
  deriving (Applicative, Cat.Category, Choice, Closed, Cochoice, Costrong, Env e, Functor, Mapping, Monad, Profunctor, Co.Representable, Res r, Strong, Traversing)

instance Distributive (C e) where
  distribute = distributeRep
  collect = collectRep

instance Sieve C Identity where
  sieve = fmap Identity . runC

instance Cosieve C Identity where
  cosieve = lmap runIdentity . runC

instance Pro.Representable C where
  type Rep C = Identity
  tabulate = C . fmap runIdentity

instance Pro.Corepresentable C where
  type Corep C = Identity
  cotabulate = C . lmap Identity


-- Computation

mapCKV :: (forall x . K r x -> K r' x) -> (forall x . V e x -> V e' x) -> (C e r -> C e' r')
mapCKV f g = over _C (under _K f . under _V g)

mapCK :: (forall x . K r x -> K r' x) -> (C e r -> C e r')
mapCK = over _C . under _K

mapCV :: (forall x . V e x -> V e' x) -> (C e r -> C e' r)
mapCV = over _C . under _V


(•∘) :: (Env e c, Res r c) => K r a -> V e a -> c
k •∘ v = env (\ e -> res (k • v ∘ e))
