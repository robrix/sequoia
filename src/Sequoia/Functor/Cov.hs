{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- | A covariant functor over a profunctor’s output.
module Sequoia.Functor.Cov
( Cov(..)
) where

import           Data.Distributive
import           Data.Functor.Adjunction
import           Data.Functor.Rep
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve
import qualified Sequoia.Profunctor.Adjunction as Pro

newtype Cov p s a = Cov { runCov :: p s a }
  deriving (Choice, Closed, Cochoice, Costrong, Profunctor, Strong)

instance Profunctor p => Functor (Cov p s) where
  fmap f = Cov . rmap f . runCov

instance Pro.Corepresentable p => Distributive (Cov p s) where
  distribute = distributeRep
  collect = collectRep

instance Pro.Corepresentable p => Representable (Cov p s) where
  type Rep (Cov p s) = Pro.Corep p s
  tabulate = Cov . Pro.cotabulate
  index = cosieve . runCov

instance Pro.Adjunction p q => Adjunction (Cov p r) (Cov q r) where
  leftAdjunct  f a = Cov (Pro.leftAdjunct  (f . Cov) a)
  rightAdjunct f a = Pro.rightAdjunct (runCov . f) (runCov a)
