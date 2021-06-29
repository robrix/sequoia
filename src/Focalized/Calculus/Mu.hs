{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Focalized.Calculus.Mu
( -- * Recursion
  Recursion(..)
, muL'
  -- * Connectives
, module Focalized.Mu
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Function
import Focalized.Mu
import Focalized.Polarity
import Focalized.Quantification
import Prelude hiding (init)

-- Recursion

class Recursion r s | s -> r where
  muL
    :: ((Neg ==> Pos) f, Neg a)
    => _Γ -|s|- _Δ > f a ~~r~> a   ->   a < _Γ -|s|- _Δ
    -- ------------------------------------------------
    ->              Mu r f < _Γ -|s|- _Δ

  muR
    :: (Neg ==> Pos) f
    => _Γ -|s|- _Δ > ForAll r N (MuF r f)
    -- ----------------------------------
    -> _Γ -|s|- _Δ >             Mu  r f


muL'
  :: (Weaken s, Exchange s, Recursion r s, (Neg ==> Pos) f)
  =>             Mu  r f  < _Γ -|s|- _Δ
  -- ----------------------------------
  -> ForAll r N (MuF r f) < _Γ -|s|- _Δ
muL' p = muR init >>> wkL' p
