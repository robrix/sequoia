{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Functor.K
( K(..)
) where

import Data.Functor.Contravariant
import Data.Functor.Identity
import Sequoia.Confunctor

newtype K r a = K { runK :: a -> r }
  deriving (Monoid, Semigroup)
  deriving (Contravariant) via Flip (->) r
  deriving (Confunctor, Contrachoice, Contraclosed, Contracochoice, Contracosieve Identity, Contracostrong, Contracorepresentable, Contrarepresentable, Contrasieve Identity, Contrastrong) via Flip (->)
