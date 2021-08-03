module Sequoia.Printer.Sequent
( -- * Printable sequents
  Seq(..)
) where

import Sequoia.Printer

-- Printable sequents

newtype Seq e r _Γ _Δ = Seq { runSeq :: Printer _Δ -> Printer _Γ }
