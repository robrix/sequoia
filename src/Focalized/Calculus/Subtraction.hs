module Focalized.Calculus.Subtraction
( -- * Subtraction
  SubtractionIntro(..)
, subL'
  -- * Connectives
, module Focalized.Connective.Subtraction
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Subtraction
import Focalized.Polarity
import Prelude hiding (init)

-- Subtraction

class SubtractionIntro s where
  subL
    :: (Pos a, Neg b)
    =>         a < _Γ -|s r|- _Δ > b
    -- -----------------------------
    -> a ~-r-< b < _Γ -|s r|- _Δ

  subR
    :: (Pos a, Neg b)
    => _Γ -|s r|- _Δ > a   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->        _Γ -|s r|- _Δ > a ~-r-< b


subL'
  :: (Weaken s, Exchange s, SubtractionIntro s, Pos a, Neg b)
  => a ~-r-< b < _Γ -|s r|- _Δ
  -- -----------------------------
  ->         a < _Γ -|s r|- _Δ > b
subL' p = subR init init >>> wkR (wkL' p)
