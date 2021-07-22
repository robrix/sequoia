{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Continuation
( -- * Continuation profunctor
  type (•)(..)
  -- * Coercion
, _K
  -- * Composition
, idK
, (<••>)
, (<•••>)
  -- * Ambient control
, Res(..)
, cont
, (••)
) where

import Control.Applicative (liftA2)
import Control.Category (Category)
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing
import Sequoia.Disjunction
import Sequoia.Optic.Iso
import Sequoia.Profunctor.Recall

-- Continuation profunctor

newtype a • r = K { (•) :: a -> r }
  deriving (Applicative, Category, Choice, Closed, Cochoice, Pro.Corepresentable, Costrong, Functor, Mapping, Monad, Profunctor, Co.Representable, Pro.Representable, Res r, Strong, Traversing)

infixl 7 •

instance Distributive ((•) a) where
  distribute = distributeRep
  collect = collectRep

instance Sieve (•) Identity where
  sieve = rmap Identity . (•)

instance Cosieve (•) Identity where
  cosieve = lmap runIdentity . (•)


-- Coercion

_K :: Iso (a • r) (a' • r') (a -> r) (a' -> r')
_K = coerced


-- Composition

idK :: a • a
idK = K id


(<••>) :: Disj d => a • r -> b • r -> (a `d` b) • r
a <••> b = K ((a •) <--> (b •))

infix 3 <••>

(<•••>) :: Disj d => (e -> a • r) -> (e -> b • r) -> (e -> (a `d` b) • r)
(<•••>) = liftA2 (<••>)

infix 3 <•••>


-- Ambient control

class Res r c | c -> r where
  res :: r -> c
  liftRes :: ((c -> r) -> c) -> c

instance Res r (a -> r) where
  res = pure
  liftRes f = f =<< flip ($)

deriving instance Res r (Forget r a b)
deriving instance Res r (Recall e a r)

cont :: Res r c => (((a -> c) -> a • r) -> c) -> c
cont f = liftRes (\ run -> f (K . (run .)))

(••) :: Res r c => a • r -> a -> c
k •• v = res (k • v)

infix 7 ••
