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

class Core s => NuIntro s where
  nuL
    :: (Pos ==> Neg) f
    => Exists (K s) P (NuF (K s) f) < _Γ -|s|- _Δ
    -- ------------------------------------------
    ->                 Nu  (K s) f  < _Γ -|s|- _Δ

  nuR
    :: (Pos ==> Neg) f
    => _Γ -|s|- _Δ > Exists (K s) P (NuF (K s) f)
    -- ------------------------------------------
    -> _Γ -|s|- _Δ >                 Nu  (K s) f


nuR'
  :: (Weaken s, Exchange s, NuIntro s, (Pos ==> Neg) f)
  => _Γ -|s|- _Δ >                 Nu  (K s) f
  -- ------------------------------------------
  -> _Γ -|s|- _Δ > Exists (K s) P (NuF (K s) f)
nuR' p = wkR' p >>> nuL init
