module Focalized.Calculus.Down
( -- * Positive shift
  PosShift(..)
, downL'
, downR'
  -- * Connectives
, module Focalized.Down
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Down
import Focalized.Polarity
import Prelude hiding (init)

-- Positive shift

class PosShift s where
  downL
    :: Neg a
    =>      a < _Γ -|s r|- _Δ
    -- ----------------------
    -> Down a < _Γ -|s r|- _Δ

  downR
    :: Neg a
    => _Γ -|s r|- _Δ >      a
    -- ----------------------
    -> _Γ -|s r|- _Δ > Down a


downL'
  :: (Weaken s, Exchange s, PosShift s, Neg a)
  => Down a < _Γ -|s r|- _Δ
  -- ----------------------
  ->      a < _Γ -|s r|- _Δ
downL' p = downR init >>> wkL' p

downR'
  :: (Weaken s, Exchange s, PosShift s, Neg a)
  => _Γ -|s r|- _Δ > Down a
  -- ----------------------
  -> _Γ -|s r|- _Δ >      a
downR' p = wkR' p >>> downL init
