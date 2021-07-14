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

class Core k v s => MuIntro k v s where
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
  :: (Weaken k v s, Exchange k v s, MuIntro k v s, (Neg ==> Pos) f)
  =>             Mu  k f  < _Γ -|s|- _Δ
  -- ----------------------------------
  -> ForAll k N (MuF k f) < _Γ -|s|- _Δ
muL' p = muR init >>> wkL' p
