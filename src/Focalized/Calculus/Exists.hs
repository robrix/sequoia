{-# LANGUAGE FunctionalDependencies #-}
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

class Existential r s | s -> r where
  existsL
    :: (forall x . Polarized n x => f x < _Γ -|s|- _Δ)
    -- -----------------------------------------------
    ->                   Exists r n f   < _Γ -|s|- _Δ

  existsR
    :: (Polarized n x, Pos (f x))
    => _Γ -|s|- _Δ >            f x
    -- ----------------------------
    -> _Γ -|s|- _Δ > Exists r n f


existsL'
  :: (Weaken s, Exchange s, Existential r s, (Polarized n ==> Pos) f)
  =>                   Exists r n f   < _Γ -|s|- _Δ
  -- -----------------------------------------------
  -> (forall x . Polarized n x => f x < _Γ -|s|- _Δ)
existsL' p = existsR init >>> wkL' p
