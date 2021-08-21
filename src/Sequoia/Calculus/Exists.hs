{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Calculus.Exists
( -- * Existential quantification
  ExistentialIntro(..)
, existsL'
  -- * Connectives
, module Sequoia.Connective.Exists
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Connective.Exists
import Sequoia.Connective.Quantification
import Sequoia.Polarity

-- Existential quantification

class Core s => ExistentialIntro s where
  existsL
    :: (forall x . Polarized n x => f x < _Γ ⊣s e r⊢ _Δ)
    -- ---------------------------------------------------
    ->                   Exists r n f   < _Γ ⊣s e r⊢ _Δ

  existsR
    :: (Polarized n x, Pos (f x))
    => _Γ ⊣s e r⊢ _Δ >            f x
    -- --------------------------------
    -> _Γ ⊣s e r⊢ _Δ > Exists k n f


existsL'
  :: (Weaken s, Exchange s, ExistentialIntro s, (Polarized n ==> Pos) f)
  =>                   Exists k n f   < _Γ ⊣s e r⊢ _Δ
  -- ---------------------------------------------------
  -> (forall x . Polarized n x => f x < _Γ ⊣s e r⊢ _Δ)
existsL' p = existsR init >>> wkL' p
