{-# LANGUAGE TypeFamilies #-}
-- | A contravariant functor over a profunctor’s input.
module Sequoia.Functor.Con
( Con(..)
) where

import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Adjunction
import           Data.Functor.Contravariant.Rep
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve

newtype Con p r a = Con { runCon :: p a r }

instance Profunctor p => Contravariant (Con p r) where
  contramap f = Con . lmap f . runCon

instance Pro.Representable p => Representable (Con p r) where
  type Rep (Con p r) = Pro.Rep p r
  tabulate = Con . Pro.tabulate
  index = sieve . runCon

instance Pro.Representable p => Adjunction (Con p r) (Con p r) where
  leftAdjunct  f a = tabulate ((`index` a) . f)
  rightAdjunct f a = tabulate ((`index` a) . f)
