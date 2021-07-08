{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- | A covariant functor over a profunctor’s output.
module Sequoia.Functor.Cov
( Cov(..)
) where

import Data.Distributive
import Data.Functor.Rep
import Data.Profunctor
import Data.Profunctor.Rep (Corepresentable(..))
import Data.Profunctor.Sieve

newtype Cov p s a = Cov { runCov :: p s a }
  deriving (Choice, Closed, Cochoice, Costrong, Profunctor, Strong)

instance Profunctor p => Functor (Cov p s) where
  fmap f = Cov . rmap f . runCov

instance Corepresentable p => Distributive (Cov p s) where
  distribute = distributeRep
  collect = collectRep

instance Corepresentable p => Representable (Cov p s) where
  type Rep (Cov p s) = Corep p s
  tabulate = Cov . cotabulate
  index = cosieve . runCov
