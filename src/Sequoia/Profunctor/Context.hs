{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Context
( -- * Context & control profunctor
  _C
, type (==>)(..)
  -- * Composition
, (•<<)
, (>>•)
  -- * Computation
, mapCKV
, mapCK
, mapCV
, (•∘)
) where

import Control.Arrow
import Control.Category as Cat (Category)
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing
import Sequoia.Optic.Iso
import Sequoia.Optic.Setter
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Context & control profunctor

_C :: Iso (e ==> r) (e' ==> r') (e -> r) (e' -> r')
_C = coerced

newtype e ==> r = C { (<==) :: e -> r }
  deriving (Applicative, Arrow, ArrowApply, ArrowChoice, ArrowLoop, Cat.Category, Choice, Closed, Cochoice, Costrong, Env e, Functor, Mapping, Monad, Profunctor, Co.Representable, Res r, Strong, Traversing)

infix 6 ==>
infixl 6 <==

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


-- Composition

(•<<) :: r • s -> e ==> r -> e ==> s
(•<<) = rmap . (•)

(>>•) :: e ==> r -> r • s -> e ==> s
c >>• k = rmap (k •) c

infixr 1 •<<, >>•


-- Computation

mapCKV :: (forall x . x • r -> x • r') -> (forall x . e ∘ x -> e' ∘ x) -> (e ==> r -> e' ==> r')
mapCKV f g = over _C (under _K f . under _V g)

mapCK :: (forall x . x • r -> x • r') -> (e ==> r -> e ==> r')
mapCK = over _C . under _K

mapCV :: (forall x . e ∘ x -> e' ∘ x) -> (e ==> r -> e' ==> r)
mapCV = over _C . under _V


(•∘) :: (Env e c, Res r c) => a • r -> e ∘ a -> c
k •∘ v = env (\ e -> res (k • v ∘ e))
