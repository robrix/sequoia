{-# LANGUAGE TypeFamilies #-}
-- | A contravariant functor over a profunctor’s input.
module Sequoia.Functor.In
( In(..)
) where

import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Rep
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve

newtype In p r a = In { runIn :: p a r }

instance Profunctor p => Contravariant (In p r) where
  contramap f = In . lmap f . runIn

instance Pro.Representable p => Representable (In p r) where
  type Rep (In p r) = Pro.Rep p r
  tabulate = In . Pro.tabulate
  index = sieve . runIn
