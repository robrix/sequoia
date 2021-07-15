{-# LANGUAGE QuantifiedConstraints #-}
module Sequoia.Calculus.Nu
( -- * Corecursion
  NuIntro(..)
, nuR'
  -- * Connectives
, module Sequoia.Connective.Nu
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Nu
import Sequoia.Connective.Quantification
import Sequoia.Polarity

-- Corecursion

class Core r e s => NuIntro r e s where
  nuL
    :: (Pos ==> Neg) f
    => Exists r P (NuF r e f) < _Γ -|s|- _Δ
    -- ------------------------------------
    ->             Nu  r e f  < _Γ -|s|- _Δ

  nuR
    :: (Pos ==> Neg) f
    => _Γ -|s|- _Δ > Exists r P (NuF r e f)
    -- ------------------------------------
    -> _Γ -|s|- _Δ >             Nu  r e f


nuR'
  :: (Weaken r e s, Exchange r e s, NuIntro r e s, (Pos ==> Neg) f)
  => _Γ -|s|- _Δ >             Nu  r e f
  -- ------------------------------------
  -> _Γ -|s|- _Δ > Exists r P (NuF r e f)
nuR' p = wkR' p >>> nuL init
