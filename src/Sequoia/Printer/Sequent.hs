module Sequoia.Printer.Sequent
( -- * Printable sequents
  Seq(..)
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Sequoia.Printer

-- Printable sequents

newtype Seq e r _Γ _Δ = Seq { runSeq :: Printer _Δ -> Printer _Γ }

instance Profunctor (Seq e r) where
  dimap f g = Seq . dimap (contramap g) (contramap f) . runSeq
