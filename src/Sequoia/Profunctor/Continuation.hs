{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Continuation
( -- * Continuation profunctor
  type (•)(..)
  -- * Construction
, idK
, constK
  -- * Coercion
, _K
  -- * Double negation
, type (••)
, dn
, (=<<^)
, (^>>=)
, DN(..)
  -- * Triple negation
, type (•••)
, tnE
) where

import Control.Category (Category)
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing
import Fresnel.Iso

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

constK :: r -> a • r
constK = K . const


-- Coercion

_K :: Iso (a • r) (a' • r') (a -> r) (a' -> r')
_K = coerced


-- Double negation

type a ••r = a • r • r

infixl 7 ••

dn :: a -> a •• r
dn a = K (• a)


(=<<^) :: (a -> b •• r) -> (a •• r -> b •• r)
f =<<^ m = K (\ k -> m • K ((• k) . f))

(^>>=) :: a •• r -> (a -> b •• r) -> b •• r
m ^>>= f = K (\ k -> m • K ((• k) . f))


newtype DN r a = DN { runDN :: a •• r }

instance Functor (DN r) where
  fmap f = DN . lmap (lmap f) . runDN

instance Applicative (DN r) where
  pure = DN . dn
  DN f <*> DN a = DN (K (\ k -> f • K (\ f -> a • K (\ a -> k • f a))))

instance Monad (DN r) where
  DN m >>= f = DN (m ^>>= (runDN . f))


-- Triple negation

type a •••r = a • r • r • r

infixl 7 •••

tnE :: a ••• r -> a • r
tnE ta = K ((ta •) . dn)
