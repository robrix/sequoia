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
import           Data.Profunctor.Sieve
import           Sequoia.Functor.Applicative
import qualified Sequoia.Profunctor.Adjunction as Pro
import qualified Sequoia.Profunctor.Applicative as Pro

newtype Con p r a = Con { runCon :: p a r }

instance Profunctor p => Contravariant (Con p r) where
  contramap f = Con . lmap f . runCon

instance Pro.Representable p => Representable (Con p r) where
  type Rep (Con p r) = Pro.Rep p r
  tabulate = Con . Pro.tabulate
  index = sieve . runCon

instance Pro.Coadjunction p q => Adjunction (Con p r) (Con q r) where
  leftAdjunct  f a = Con (Pro.leftCoadjunct  (runCon . f) a)
  rightAdjunct f a = Con (Pro.rightCoadjunct (runCon . f) a)

instance Pro.Coapply c p => Contrapply c (Con p r) where
  coliftC2 f (Con a) (Con b) = Con (Pro.coliftC2 f a b)
  Con a <&> Con b = Con (a Pro.<&> b)

instance Pro.Coapplicative c p => Contrapplicative c (Con p r) where
  copure = Con . Pro.copure
