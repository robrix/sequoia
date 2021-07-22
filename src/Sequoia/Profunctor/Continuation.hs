{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Continuation
( -- * Continuation profunctor
  K(..)
  -- * Coercion
, _K
  -- * Composition
, idK
, (<••>)
  -- * Ambient control
, Res(..)
, cont
, (••)
) where

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

newtype K a r = K { (•) :: a -> r }
  deriving (Applicative, Category, Choice, Closed, Cochoice, Pro.Corepresentable, Costrong, Functor, Mapping, Monad, Profunctor, Co.Representable, Pro.Representable, Res r, Strong, Traversing)

infixl 7 •

instance Distributive (K r) where
  distribute = distributeRep
  collect = collectRep

instance Sieve K Identity where
  sieve = rmap Identity . (•)

instance Cosieve K Identity where
  cosieve = lmap runIdentity . (•)


-- Coercion

_K :: Iso (K a r) (K a' r') (a -> r) (a' -> r')
_K = coerced


-- Composition

idK :: K a a
idK = K id


(<••>) :: Disj d => K a r -> K b r -> K (a `d` b) r
a <••> b = K ((a •) <--> (b •))

infix 3 <••>


-- Ambient control

class Res r c | c -> r where
  res :: r -> c
  liftRes :: ((c -> r) -> c) -> c

instance Res r (a -> r) where
  res = pure
  liftRes f = f =<< flip ($)

deriving instance Res r (Forget r a b)
deriving instance Res r (Recall e a r)

cont :: Res r c => (((a -> c) -> K a r) -> c) -> c
cont f = liftRes (\ run -> f (K . (run .)))

(••) :: Res r c => K a r -> a -> c
k •• v = res (k • v)

infix 7 ••
