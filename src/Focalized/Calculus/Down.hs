module Focalized.Calculus.Down
( -- * Down
  DownIntro(..)
, downL'
, downR'
  -- * Connectives
, module Focalized.Connective.Down
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Down
import Focalized.Polarity
import Prelude hiding (init)

-- Down

class Core s => DownIntro s where
  downL
    :: Neg a
    =>      a < _Γ -|s|- _Δ
    -- --------------------
    -> Down a < _Γ -|s|- _Δ

  downR
    :: Neg a
    => _Γ -|s|- _Δ >      a
    -- --------------------
    -> _Γ -|s|- _Δ > Down a


downL'
  :: (Weaken s, Exchange s, DownIntro s, Neg a)
  => Down a < _Γ -|s|- _Δ
  -- --------------------
  ->      a < _Γ -|s|- _Δ
downL' p = downR init >>> wkL' p

downR'
  :: (Weaken s, Exchange s, DownIntro s, Neg a)
  => _Γ -|s|- _Δ > Down a
  -- --------------------
  -> _Γ -|s|- _Δ >      a
downR' p = wkR' p >>> downL init
