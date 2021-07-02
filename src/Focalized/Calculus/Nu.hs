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

class NuIntro s where
  nuL
    :: (Pos ==> Neg) f
    => Exists r P (NuF r f) < _Γ -|s r|- _Δ
    -- ------------------------------------
    ->             Nu  r f  < _Γ -|s r|- _Δ

  nuR
    :: (Pos ==> Neg) f
    => _Γ -|s r|- _Δ > Exists r P (NuF r f)
    -- ------------------------------------
    -> _Γ -|s r|- _Δ >             Nu  r f


nuR'
  :: (Weaken s, Exchange s, NuIntro s, (Pos ==> Neg) f)
  => _Γ -|s r|- _Δ >             Nu  r f
  -- ------------------------------------
  -> _Γ -|s r|- _Δ > Exists r P (NuF r f)
nuR' p = wkR' p >>> nuL init
