{-# LANGUAGE QuantifiedConstraints #-}
module Sequoia.Calculus.Mu
( -- * Recursion
  MuIntro(..)
, muL'
  -- * Connectives
, module Sequoia.Connective.Mu
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Function
import Sequoia.Connective.Mu
import Sequoia.Connective.Quantification
import Sequoia.Polarity
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
