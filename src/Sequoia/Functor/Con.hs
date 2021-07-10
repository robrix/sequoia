{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- | A contravariant functor over a profunctor’s input.
module Sequoia.Functor.Con
( Con(..)
) where

import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Adjunction
import           Data.Functor.Contravariant.Rep
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import qualified Sequoia.Profunctor.Adjunction as Pro

newtype Con p r a = Con { runCon :: p a r }

instance Profunctor p => Contravariant (Con p r) where
  contramap f = Con . lmap f . runCon

instance (Pro.Coadjunction q p, Pro.Corep p ~ q ()) => Representable (Con p r) where
  type Rep (Con p r) = Pro.Corep p r
  tabulate = Con . Pro.cotabulateCoadjunction
  index = Pro.cosieveCoadjunction . runCon

instance (Pro.Coadjunction p q, Pro.Corep q ~ p ()) => Adjunction (Con p r) (Con q r) where
  leftAdjunct  f a = Con (Pro.leftCoadjunct  (runCon . f) a)
  rightAdjunct f a = Con (Pro.rightCoadjunct (runCon . f) a)
