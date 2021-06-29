module Focalized.Calculus.Par
( -- * Negative disjunction
  NegDisjunction(..)
, parR'
  -- * Connectives
, module Focalized.Par
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Par
import Focalized.Polarity
import Prelude hiding (init)

-- Negative disjunction

class NegDisjunction s where
  parL
    :: (Neg a, Neg b)
    => a < _Γ -|s|- _Δ   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->          a ⅋ b < _Γ -|s|- _Δ

  parR
    :: (Neg a, Neg b)
    => _Γ -|s|- _Δ > a > b
    -- -------------------
    -> _Γ -|s|- _Δ > a ⅋ b


parR'
  :: (Weaken s, Contextual r s, NegDisjunction s, Neg a, Neg b)
  => _Γ -|s|- _Δ > a ⅋ b
  -- -------------------
  -> _Γ -|s|- _Δ > a > b
parR' p = poppedR (wkR . wkR) p >>> parL (wkR init) init
