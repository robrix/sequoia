{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- | A covariant functor over a profunctor’s output.
module Sequoia.Functor.Cov
( Ex(..)
) where

import Data.Distributive
import Data.Functor.Rep
import Data.Profunctor
import Data.Profunctor.Rep (Corepresentable(..))
import Data.Profunctor.Sieve

newtype Ex p s a = Ex { runEx :: p s a }
  deriving (Choice, Closed, Cochoice, Costrong, Profunctor, Strong)

instance Profunctor p => Functor (Ex p s) where
  fmap f = Ex . rmap f . runEx

instance Corepresentable p => Distributive (Ex p s) where
  distribute = distributeRep
  collect = collectRep

instance Corepresentable p => Representable (Ex p s) where
  type Rep (Ex p s) = Corep p s
  tabulate = Ex . cotabulate
  index = cosieve . runEx
