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
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- Corecursion

class Core s => NuIntro s where
  nuL
    :: (Pos ==> Neg) f
    => Exists (R (K s)) P (NuF (R (K s)) f) < _Γ -|s|- _Δ
    -- -------00000000-----------------------------------
    ->                     Nu  (R (K s)) f  < _Γ -|s|- _Δ

  nuR
    :: (Pos ==> Neg) f
    => _Γ -|s|- _Δ > Exists (R (K s)) P (NuF (R (K s)) f)
    -- --------------------------------------------------
    -> _Γ -|s|- _Δ >                     Nu  (R (K s)) f


nuR'
  :: (Weaken s, Exchange s, NuIntro s, (Pos ==> Neg) f)
  => _Γ -|s|- _Δ >                     Nu  (R (K s)) f
  -- --------------------------------------------------
  -> _Γ -|s|- _Δ > Exists (R (K s)) P (NuF (R (K s)) f)
nuR' p = wkR' p >>> nuL init
