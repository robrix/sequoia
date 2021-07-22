{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Continuation
( -- * Continuation profunctor
  K(..)
) where

import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing

-- Continuation profunctor

newtype K a r = K { runK :: a -> r }
  deriving (Applicative, Choice, Closed, Cochoice, Pro.Corepresentable, Costrong, Functor, Mapping, Monad, Profunctor, Co.Representable, Pro.Representable, Strong, Traversing)

instance Distributive (K r) where
  distribute = distributeRep
  collect = collectRep

instance Sieve K Identity where
  sieve = rmap Identity . runK

instance Cosieve K Identity where
  cosieve = lmap runIdentity . runK
