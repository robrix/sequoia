module Sequoia.Print.Sequent
( -- * Printable sequents
  Seq(..)
  -- * Elimination
, appSeq
, printSeq
) where

import Control.Monad (ap)
import Data.Profunctor
import Prelude hiding (print)
import Sequoia.Calculus.Core
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Print.Doc
import Sequoia.Print.Printer

-- Printable sequents

newtype Seq e r _Γ _Δ = Seq { runSeq :: Printer r _Δ Doc -> Printer r _Γ Doc }

instance Profunctor (Seq e r) where
  dimap f g = Seq . dimap (lmap g) (lmap f) . runSeq

instance Functor (Seq e r _Γ) where
  fmap = rmap

instance Applicative (Seq e r _Γ) where
  pure = Seq . lmap . const
  (<*>) = ap

instance Monad (Seq e r _Γ) where
  Seq r >>= f = Seq (\ _Δ -> printer (\ k _Γ -> getPrint (r (lmap f (printSeq _Γ _Δ))) k _Γ))


-- Elimination

appSeq :: Seq e r _Γ _Δ -> _Γ -> Printer r _Δ Doc -> (Doc -> r) -> r
appSeq s _Γ pΔ k = getPrint (runSeq s pΔ) k _Γ

printSeq :: _Γ -> Printer r _Δ Doc -> Printer r (Seq e r _Γ _Δ) Doc
printSeq _Γ _Δ = printer (\ k s -> appSeq s _Γ _Δ k)


-- Core

instance Core Seq where
  l >>> r = l >>= pure <--> \ a -> lmap (a >--<) r
  init = Seq (dimap (lmap inr) (lmap exl) id)
