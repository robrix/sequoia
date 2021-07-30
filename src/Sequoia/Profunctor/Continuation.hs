{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Continuation
( -- * Continuation profunctor
  type (•)(..)
  -- * Construction
, idK
, inK
, cont
  -- * Coercion
, _K
  -- * Computation
, (<••>)
, (<•••>)
  -- * Double negation
, type (••)
, dn
, DN(..)
  -- * Triple negation
, type (•••)
, tnE
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
import Sequoia.Monad.Run
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


-- Construction

idK :: a • a
idK = K id

inK :: MonadRun m => (a -> m r) -> m (a • r)
inK = fmap K . fn

cont :: MonadRun m => ((forall b . (b -> m r) -> b • r) -> m a) -> m a
cont f = withRun (\ run -> f (K . (run .)))


-- Coercion

_K :: Iso (a • r) (a' • r') (a -> r) (a' -> r')
_K = coerced


-- Computation

(<••>) :: Disj d => a • r -> b • r -> (a `d` b) • r
a <••> b = K ((a •) <--> (b •))

infix 3 <••>

(<•••>) :: Disj d => (e -> a • r) -> (e -> b • r) -> (e -> (a `d` b) • r)
(<•••>) = liftA2 (<••>)

infix 3 <•••>


-- Double negation

type a ••r = a • r • r

dn :: a -> a •• r
dn a = K (• a)


newtype DN r a = DN { runDN :: a •• r }

instance Functor (DN r) where
  fmap f = DN . lmap (lmap f) . runDN


-- Triple negation

type a •••r = a • r • r • r

tnE :: a ••• r -> a • r
tnE ta = K ((ta •) . dn)
