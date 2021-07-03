{-# LANGUAGE QuantifiedConstraints #-}
module Focalized.Calculus.Mu
( -- * Recursion
  MuIntro(..)
, muL'
  -- * Connectives
, module Focalized.Connective.Mu
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Function
import Focalized.Connective.Mu
import Focalized.Connective.Quantification
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- Recursion

class MuIntro s where
  muL
    :: ((Neg ==> Pos) f, Neg a)
    => _Γ -|s|- _Δ > f a ~~R (K s)~> a   ->   a < _Γ -|s|- _Δ
    -- ------------------------------------------------------
    ->              Mu (R (K s)) f < _Γ -|s|- _Δ

  muR
    :: (Neg ==> Pos) f
    => _Γ -|s|- _Δ > ForAll (R (K s)) N (MuF (R (K s)) f)
    -- --------------------------------------------------
    -> _Γ -|s|- _Δ >                     Mu  (R (K s)) f


muL'
  :: (Weaken s, Exchange s, MuIntro s, (Neg ==> Pos) f)
  =>                     Mu  (R (K s)) f  < _Γ -|s|- _Δ
  -- --------------------------------------------------
  -> ForAll (R (K s)) N (MuF (R (K s)) f) < _Γ -|s|- _Δ
muL' p = muR init >>> wkL' p
