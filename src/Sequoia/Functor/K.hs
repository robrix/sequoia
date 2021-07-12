{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Functor.K
( K(..)
) where

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Adjunction
import Data.Functor.Contravariant.Rep
import Data.Functor.Identity
import Sequoia.Confunctor

newtype K r a = K { runK :: a -> r }
  deriving (Monoid, Semigroup)
  deriving (Contravariant, Representable) via Flip (->) r
  deriving (Confunctor, Contrachoice, Contraclosed, Contracochoice, Contracosieve Identity, Contracostrong, Contracorepresentable, Contrarepresentable, Contrasieve Identity, Contrastrong) via Flip (->)

instance Adjunction (K r) (K r) where
  leftAdjunct  f a = K ((`runK` a) . f)
  rightAdjunct f b = K ((`runK` b) . f)
