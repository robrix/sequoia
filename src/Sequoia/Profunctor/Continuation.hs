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
  -- * Double negation
, type (••)
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

-- Continuation profunctor

newtype a • r = K { (•) :: a -> r }
  deriving (Applicative, Category, Choice, Closed, Cochoice, Pro.Corepresentable, Costrong, Functor, Mapping, Monad, Profunctor, Co.Representable, Pro.Representable, Strong, Traversing)

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


-- Double negation

type a ••r = a • r • r
