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
import Focalized.Polarity
import Prelude hiding (init)

-- Recursion

class Core k s => MuIntro k s where
  muL
    :: ((Neg ==> Pos) f, Neg a)
    => _Γ -|s|- _Δ > f a ~~k~> a   ->   a < _Γ -|s|- _Δ
    -- ------------------------------------------------
    ->              Mu k f < _Γ -|s|- _Δ

  muR
    :: (Neg ==> Pos) f
    => _Γ -|s|- _Δ > ForAll k N (MuF k f)
    -- ----------------------------------
    -> _Γ -|s|- _Δ >             Mu  k f


muL'
  :: (Weaken k s, Exchange k s, MuIntro k s, (Neg ==> Pos) f)
  =>             Mu  k f  < _Γ -|s|- _Δ
  -- ----------------------------------
  -> ForAll k N (MuF k f) < _Γ -|s|- _Δ
muL' p = muR init >>> wkL' p
