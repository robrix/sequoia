module Sequoia.Calculus.Subtraction
( -- * Subtraction
  SubtractionIntro(..)
, subL'
  -- * Connectives
, module Sequoia.Connective.Subtraction
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Subtraction
import Sequoia.Polarity
import Prelude hiding (init)

-- Subtraction

class Core k s => SubtractionIntro k s where
  subL
    :: (Pos a, Neg b)
    =>         a < _Γ -|s|- _Δ > b
    -- ---------------------------
    -> a ~-k-< b < _Γ -|s|- _Δ

  subR, (⊢-<)
    :: (Pos a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->       _Γ -|s|- _Δ > a ~-k-< b
  (⊢-<) = subR

  infixr 5 ⊢-<


subL'
  :: (Weaken k s, Exchange k s, SubtractionIntro k s, Pos a, Neg b)
  => a ~-k-< b < _Γ -|s|- _Δ
  -- ---------------------------
  ->         a < _Γ -|s|- _Δ > b
subL' p = subR init init >>> wkR (wkL' p)
