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

class Core s => MuIntro s where
  muL
    :: ((Neg ==> Pos) f, Neg a)
    => _Γ -|s e r|- _Δ > f a ~~Fun e r~> a   ->   a < _Γ -|s e r|- _Δ
    -- --------------------------------------------------------------
    ->                 Mu e r f < _Γ -|s e r|- _Δ

  muR
    :: (Neg ==> Pos) f
    => _Γ -|s e r|- _Δ > ForAll r N (MuF e r f)
    -- ----------------------------------------
    -> _Γ -|s e r|- _Δ >             Mu  e r f


muL'
  :: (Weaken s, Exchange s, MuIntro s, (Neg ==> Pos) f)
  =>             Mu  e r f  < _Γ -|s e r|- _Δ
  -- ----------------------------------------
  -> ForAll r N (MuF e r f) < _Γ -|s e r|- _Δ
muL' p = muR init >>> wkL' p
