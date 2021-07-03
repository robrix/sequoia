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
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- Subtraction

class Core s => SubtractionIntro s where
  subL
    :: (Pos a, Neg b)
    =>         a < _Γ -|s|- _Δ > b
    -- ---------------------------
    -> a ~-R (K s)-< b < _Γ -|s|- _Δ

  subR, (⊢-<)
    :: (Pos a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->     _Γ -|s|- _Δ > a ~-R (K s)-< b
  (⊢-<) = subR

  infixr 5 ⊢-<


subL'
  :: (Weaken s, Exchange s, SubtractionIntro s, Pos a, Neg b)
  => a ~-R (K s)-< b < _Γ -|s|- _Δ
  -- ---------------------------------
  ->               a < _Γ -|s|- _Δ > b
subL' p = subR init init >>> wkR (wkL' p)
