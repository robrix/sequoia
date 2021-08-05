module Sequoia.Print.Sequent
( -- * Printable sequents
  Seq(..)
  -- * Elimination
, appSeq
, printSeq
) where

import Control.Monad (ap)
import Data.Functor.Contravariant
import Data.Profunctor
import Prelude hiding (print)
import Sequoia.Calculus.Core
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Print.Doc
import Sequoia.Print.Printer

-- Printable sequents

newtype Seq e r _Γ _Δ = Seq { runSeq :: Printer r _Δ -> Printer r _Γ }

instance Profunctor (Seq e r) where
  dimap f g = Seq . dimap (contramap g) (contramap f) . runSeq

instance Functor (Seq e r _Γ) where
  fmap = rmap

instance Applicative (Seq e r _Γ) where
  pure = Seq . contramap . const
  (<*>) = ap

instance Monad (Seq e r _Γ) where
  Seq r >>= f = Seq (\ _Δ -> Printer (\ k _Γ -> runPrint (r (contramap f (printSeq _Γ _Δ))) k _Γ))


-- Elimination

appSeq :: Seq e r _Γ _Δ -> _Γ -> Printer r _Δ -> (Doc -> r) -> r
appSeq s _Γ pΔ k = runPrint (runSeq s pΔ) k _Γ

printSeq :: _Γ -> Printer r _Δ -> Printer r (Seq e r _Γ _Δ)
printSeq _Γ _Δ = Printer (\ k s -> appSeq s _Γ _Δ k)


-- Core

instance Core Seq where
  l >>> r = l >>= pure <--> \ a -> lmap (a >--<) r
  init = Seq (dimap (contramap inr) (contramap exl) id)
