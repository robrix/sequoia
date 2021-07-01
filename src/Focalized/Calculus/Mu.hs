{-# LANGUAGE QuantifiedConstraints #-}
module Focalized.Calculus.Mu
( -- * Recursion
  MuIntro(..)
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

class MuIntro s where
  muL
    :: ((Neg ==> Pos) f, Neg a)
    => _Γ -|s r|- _Δ > f a ~~r~> a   ->   a < _Γ -|s r|- _Δ
    -- ----------------------------------------------------
    ->              Mu r f < _Γ -|s r|- _Δ

  muR
    :: (Neg ==> Pos) f
    => _Γ -|s r|- _Δ > ForAll r N (MuF r f)
    -- ------------------------------------
    -> _Γ -|s r|- _Δ >             Mu  r f


muL'
  :: (Weaken s, Exchange s, MuIntro s, (Neg ==> Pos) f)
  =>             Mu  r f  < _Γ -|s r|- _Δ
  -- ------------------------------------
  -> ForAll r N (MuF r f) < _Γ -|s r|- _Δ
muL' p = muR init >>> wkL' p
