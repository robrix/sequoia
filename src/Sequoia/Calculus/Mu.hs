{-# LANGUAGE QuantifiedConstraints #-}
module Sequoia.Calculus.Mu
( -- * Recursion
  MuIntro(..)
, muL'
  -- * Connectives
, module Sequoia.Connective.Mu
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Function
import Sequoia.Connective.Mu
import Sequoia.Connective.Quantification
import Sequoia.Polarity

-- Recursion

class Core r e s => MuIntro r e s where
  muL
    :: ((Neg ==> Pos) f, Neg a)
    => _Γ -|s|- _Δ > f a ~~Fun r e~> a   ->   a < _Γ -|s|- _Δ
    -- ------------------------------------------------------
    ->                 Mu r e f < _Γ -|s|- _Δ

  muR
    :: (Neg ==> Pos) f
    => _Γ -|s|- _Δ > ForAll r N (MuF r e f)
    -- ------------------------------------
    -> _Γ -|s|- _Δ >             Mu  r e f


muL'
  :: (Weaken r e s, Exchange r e s, MuIntro r e s, (Neg ==> Pos) f)
  =>             Mu  r e f  < _Γ -|s|- _Δ
  -- ------------------------------------
  -> ForAll r N (MuF r e f) < _Γ -|s|- _Δ
muL' p = muR init >>> wkL' p
