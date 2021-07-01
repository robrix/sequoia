module Focalized.Calculus.Down
( -- * Down
  DownIntro(..)
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

-- Down

class DownIntro s where
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
  :: (Weaken s, Exchange s, DownIntro s, Neg a)
  => Down a < _Γ -|s r|- _Δ
  -- ----------------------
  ->      a < _Γ -|s r|- _Δ
downL' p = downR init >>> wkL' p

downR'
  :: (Weaken s, Exchange s, DownIntro s, Neg a)
  => _Γ -|s r|- _Δ > Down a
  -- ----------------------
  -> _Γ -|s r|- _Δ >      a
downR' p = wkR' p >>> downL init
