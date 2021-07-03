{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus.Exists
( -- * Existential quantification
  ExistentialIntro(..)
, existsL'
  -- * Connectives
, module Focalized.Connective.Exists
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Exists
import Focalized.Connective.Quantification
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- Existential quantification

class Core s => ExistentialIntro s where
  existsL
    :: (forall x . Polarized n x => f x < _Γ -|s|- _Δ)
    -- -----------------------------------------------
    ->           Exists (R (K s)) n f   < _Γ -|s|- _Δ

  existsR
    :: (Polarized n x, Pos (f x))
    => _Γ -|s|- _Δ >            f x
    -- ----------------------------
    -> _Γ -|s|- _Δ > Exists (R (K s)) n f


existsL'
  :: (Weaken s, Exchange s, ExistentialIntro s, (Polarized n ==> Pos) f)
  =>           Exists (R (K s)) n f   < _Γ -|s|- _Δ
  -- -----------------------------------------------
  -> (forall x . Polarized n x => f x < _Γ -|s|- _Δ)
existsL' p = existsR init >>> wkL' p
