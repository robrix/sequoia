module Sequoia.Calculus.Subtraction
( -- * Subtraction
  SubtractionIntro(..)
, subL'
  -- * Connectives
, module Sequoia.Connective.Subtraction
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Connective.Subtraction
import Sequoia.Polarity

-- Subtraction

class Core e r s => SubtractionIntro e r s where
  subL
    :: (Pos a, Neg b)
    =>         a < _Γ -|s|- _Δ > b
    -- ---------------------------
    -> a ~-r-< b < _Γ -|s|- _Δ

  subR, (⊢-<)
    :: (Pos a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->       _Γ -|s|- _Δ > a ~-r-< b
  (⊢-<) = subR

  infixr 5 ⊢-<


subL'
  :: (Weaken e r s, Exchange e r s, SubtractionIntro e r s, Pos a, Neg b)
  => a ~-r-< b < _Γ -|s|- _Δ
  -- ---------------------------
  ->         a < _Γ -|s|- _Δ > b
subL' p = subR init init >>> wkR (wkL' p)
