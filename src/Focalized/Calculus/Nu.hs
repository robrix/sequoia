{-# LANGUAGE QuantifiedConstraints #-}
module Focalized.Calculus.Nu
( -- * Corecursion
  NuIntro(..)
, nuR'
  -- * Connectives
, module Focalized.Connective.Nu
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Nu
import Focalized.Connective.Quantification
import Focalized.Polarity
import Prelude hiding (init)

-- Corecursion

class Core k s => NuIntro k s where
  nuL
    :: (Pos ==> Neg) f
    => Exists k P (NuF k f) < _Γ -|s|- _Δ
    -- ----------------------------------
    ->             Nu  k f  < _Γ -|s|- _Δ

  nuR
    :: (Pos ==> Neg) f
    => _Γ -|s|- _Δ > Exists k P (NuF k f)
    -- ----------------------------------
    -> _Γ -|s|- _Δ >             Nu  k f


nuR'
  :: (Weaken k s, Exchange k s, NuIntro k s, (Pos ==> Neg) f)
  => _Γ -|s|- _Δ >             Nu  k f
  -- ----------------------------------
  -> _Γ -|s|- _Δ > Exists k P (NuF k f)
nuR' p = wkR' p >>> nuL init
