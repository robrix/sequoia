{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Functor.V
( V(..)
) where

import           Data.Distributive
import           Data.Functor.Identity
import           Data.Functor.Rep
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve

newtype V s a = V { runV :: s -> a }
  deriving (Applicative, Choice, Closed, Cochoice, Costrong, Functor, Monad, Monoid, Profunctor, Representable, Pro.Representable, Semigroup, Strong)

instance Distributive (V s) where
  distribute = distributeRep
  collect = collectRep

instance Sieve V Identity where
  sieve = sieve . runV

instance Cosieve V Identity where
  cosieve = cosieve . runV
