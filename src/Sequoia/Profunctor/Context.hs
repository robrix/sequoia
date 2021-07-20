{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Context
( _C
, C(..)
) where

import Control.Category as Cat (Category)
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing
import Sequoia.Continuation
import Sequoia.Optic.Iso
import Sequoia.Value

_C :: Iso (C e r) (C e' r') (e -> r) (e' -> r')
_C = runC <-> C

newtype C e r = C { runC :: e -> r }
  deriving (Applicative, Cat.Category, Choice, Closed, Cochoice, Costrong, Functor, Mapping, Monad, Profunctor, Co.Representable, Strong, Traversing)

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

instance Env C where
  env = C . (runC =<<)

instance Res C where
  res = C . const
  liftRes f = C (\ e -> runC (f (`runC` e)) e)
