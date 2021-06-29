module Focalized.Calculus.With
( -- * Negative conjunction
  NegConjunction(..)
, withR1'
, withR2'
  -- * Connectives
, module Focalized.With
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Polarity
import Focalized.With
import Prelude hiding (init)

-- Negative conjunction

class NegConjunction s where
  withL1
    :: (Neg a, Neg b)
    => a     < _Γ -|s|- _Δ
    -- -------------------
    -> a & b < _Γ -|s|- _Δ

  withL2
    :: (Neg a, Neg b)
    =>     b < _Γ -|s|- _Δ
    -- -------------------
    -> a & b < _Γ -|s|- _Δ

  withR
    :: (Neg a, Neg b)
    => _Γ -|s|- _Δ > a   ->   _Γ -|s|- _Δ > b
    -- --------------------------------------
    ->           _Γ -|s|- _Δ > a & b


withR1'
  :: (Weaken s, Exchange s, NegConjunction s, Neg a, Neg b)
  => _Γ -|s|- _Δ > a & b
  -- -------------------
  -> _Γ -|s|- _Δ > a
withR1' t = wkR' t >>> withL1 init

withR2'
  :: (Weaken s, Exchange s, NegConjunction s, Neg a, Neg b)
  => _Γ -|s|- _Δ > a & b
  -- -------------------
  -> _Γ -|s|- _Δ > b
withR2' t = wkR' t >>> withL2 init
