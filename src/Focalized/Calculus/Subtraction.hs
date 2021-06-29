{-# LANGUAGE FunctionalDependencies #-}
module Focalized.Calculus.Subtraction
( -- * Subtraction
  Subtraction(..)
, subL'
  -- * Connectives
, module Focalized.Subtraction
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Polarity
import Focalized.Subtraction
import Prelude hiding (init)

-- Subtraction

class Subtraction r s | s -> r where
  subL
    :: (Pos a, Neg b)
    =>         a < _Γ -|s|- _Δ > b
    -- ---------------------------
    -> a ~-r-< b < _Γ -|s|- _Δ

  subR
    :: (Pos a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->        _Γ -|s|- _Δ > a ~-r-< b


subL'
  :: (Weaken s, Exchange s, Subtraction r s, Pos a, Neg b)
  => a ~-r-< b < _Γ -|s|- _Δ
  -- ---------------------------
  ->         a < _Γ -|s|- _Δ > b
subL' p = subR init init >>> wkR (wkL' p)
