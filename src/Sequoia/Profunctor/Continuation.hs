{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Continuation
( -- * Continuation profunctor
  type (•)(..)
  -- * Continuation abstraction
, Continuation
, ContinuationI(..)
, ContinuationE(..)
  -- * Construction
, idK
, constK
  -- * Coercion
, _K
  -- * Defaults
, protabulateCont
, sieveCont
, cotabulateCont
, cosieveCont
  -- * Double negation
, type (••)
, dn
, (=<<^)
, (^>>=)
, (•=<<)
, (>>=•)
, DN(..)
  -- * Triple negation
, type (•••)
, tnE
) where

import Control.Category (Category)
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing
import Fresnel.Iso
import Sequoia.Profunctor

-- Continuation profunctor

newtype a • r = K { runK :: a -> r }
  deriving (Applicative, Category, Choice, Closed, Cochoice, Pro.Corepresentable, Costrong, Functor, Mapping, Monad, Profunctor, Co.Representable, Pro.Representable, Strong, Traversing)

instance Distributive ((•) a) where
  distribute = distributeRep
  collect = collectRep

instance Sieve (•) Identity where
  sieve = rmap Identity . (•)

instance Cosieve (•) Identity where
  cosieve = lmap runIdentity . (•)

instance Continuation (•)

instance ContinuationI (•) where
  inK = K

instance ContinuationE (•) where
  (•) = runK


-- Continuation abstraction

class (ContinuationE k, ContinuationI k) => Continuation k

class Profunctor k => ContinuationI k where
  inK :: (a -> r) -> k a r

class Profunctor k => ContinuationE k where
  (•) :: k a r -> (a -> r)

  infixl 8 •


-- Construction

idK :: ContinuationI k => a `k` a
idK = inK id

constK :: ContinuationI k => r -> a `k` r
constK = inK . const


-- Coercion

_K :: Iso (a • r) (a' • r') (a -> r) (a' -> r')
_K = coerced


-- Defaults

protabulateCont :: ContinuationI k => (a -> Identity b) -> a `k` b
protabulateCont = inK . rmap runIdentity

sieveCont :: ContinuationE k => a `k` b -> (a -> Identity b)
sieveCont = rmap Identity . (•)

cotabulateCont :: ContinuationI k => (Identity a -> b) -> a `k` b
cotabulateCont = inK . lmap Identity

cosieveCont :: ContinuationE k => a `k` b -> Identity a -> b
cosieveCont = lmap runIdentity . (•)


-- Double negation

type a ••r = a • r • r

infixl 8 ••

dn :: (ContinuationE j, ContinuationI k) => a -> (a `j` r) `k` r
dn a = inK (• a)


(=<<^) :: (a -> b •• r) -> (a •• r -> b •• r)
f =<<^ m = K (\ k -> m • K ((• k) . f))

infixr 1 =<<^

(^>>=) :: a •• r -> (a -> b •• r) -> b •• r
m ^>>= f = K (\ k -> m • K ((• k) . f))

infixl 1 ^>>=


(•=<<) :: Monad m => (a • m b) -> (m a -> m b)
(•=<<) = (=<<) . (•)

infixr 1 •=<<

(>>=•) :: Monad m => m a -> (a • m b) -> m b
(>>=•) = (. (•)) . (>>=)

infixl 1 >>=•


newtype DN r a = DN { runDN :: a •• r }

instance Functor (DN r) where
  fmap f = DN . (<<^ (<<^ f)) . runDN

instance Applicative (DN r) where
  pure = DN . dn
  DN f <*> DN a = DN (f <<^ (a <<^) . (<<^))

instance Monad (DN r) where
  DN m >>= f = DN (m ^>>= runDN . f)


-- Triple negation

type a •••r = a • r • r • r

infixl 8 •••

tnE :: a ••• r -> a • r
tnE = (<<^ dn)
