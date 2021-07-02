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
import Focalized.Polarity
import Prelude hiding (init)

-- Existential quantification

class ExistentialIntro s where
  existsL
    :: (forall x . Polarized n x => f x < _Γ -|s r|- _Δ)
    -- -------------------------------------------------
    ->                   Exists r n f   < _Γ -|s r|- _Δ

  existsR
    :: (Polarized n x, Pos (f x))
    => _Γ -|s r|- _Δ >            f x
    -- ------------------------------
    -> _Γ -|s r|- _Δ > Exists r n f


existsL'
  :: (Weaken s, Exchange s, ExistentialIntro s, (Polarized n ==> Pos) f)
  =>                   Exists r n f   < _Γ -|s r|- _Δ
  -- -------------------------------------------------
  -> (forall x . Polarized n x => f x < _Γ -|s r|- _Δ)
existsL' p = existsR init >>> wkL' p
