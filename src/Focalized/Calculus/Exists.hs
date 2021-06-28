{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus.Exists
( -- * Existential quantification
  Existential(..)
, existsL'
  -- * Connectives
, module Focalized.Exists
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Exists
import Focalized.Polarity
import Focalized.Quantification
import Prelude hiding (init)

-- Existential quantification

class Existential s where
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
  :: (Weaken s, Exchange s, Existential s, (Polarized n ==> Pos) f)
  =>                   Exists r n f   < _Γ -|s r|- _Δ
  -- -------------------------------------------------
  -> (forall x . Polarized n x => f x < _Γ -|s r|- _Δ)
existsL' p = existsR init >>> wkL' p
