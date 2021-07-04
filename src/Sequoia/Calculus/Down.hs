module Sequoia.Calculus.Down
( -- * Down
  DownIntro(..)
, downL'
, downR'
  -- * Connectives
, module Sequoia.Connective.Down
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Down
import Sequoia.Polarity
import Prelude hiding (init)

-- Down

class Core k s => DownIntro k s where
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
  :: (Weaken k s, Exchange k s, DownIntro k s, Neg a)
  => Down a < _Γ -|s|- _Δ
  -- --------------------
  ->      a < _Γ -|s|- _Δ
downL' p = downR init >>> wkL' p

downR'
  :: (Weaken k s, Exchange k s, DownIntro k s, Neg a)
  => _Γ -|s|- _Δ > Down a
  -- --------------------
  -> _Γ -|s|- _Δ >      a
downR' p = wkR' p >>> downL init
