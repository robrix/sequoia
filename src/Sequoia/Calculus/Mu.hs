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
import Sequoia.Calculus.Structural
import Sequoia.Connective.Function
import Sequoia.Connective.Mu
import Sequoia.Connective.Quantification
import Sequoia.Polarity

-- Recursion

class Core e r s => MuIntro e r s where
  muL
    :: ((Neg ==> Pos) f, Neg a)
    => _Γ -|s|- _Δ > f a ~~Fun e r~> a   ->   a < _Γ -|s|- _Δ
    -- ------------------------------------------------------
    ->                 Mu e r f < _Γ -|s|- _Δ

  muR
    :: (Neg ==> Pos) f
    => _Γ -|s|- _Δ > ForAll r N (MuF e r f)
    -- ------------------------------------
    -> _Γ -|s|- _Δ >             Mu  e r f


muL'
  :: (Weaken e r s, Exchange e r s, MuIntro e r s, (Neg ==> Pos) f)
  =>             Mu  e r f  < _Γ -|s|- _Δ
  -- ------------------------------------
  -> ForAll r N (MuF e r f) < _Γ -|s|- _Δ
muL' p = muR init >>> wkL' p
