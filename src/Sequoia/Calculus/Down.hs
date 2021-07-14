module Sequoia.Calculus.Down
( -- * Down
  DownIntro(..)
, downL'
, downR'
  -- * Connectives
, module Sequoia.Connective.Down
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Down
import Sequoia.Polarity

-- Down

class Core k v s => DownIntro k v s where
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
  :: (Weaken k v s, Exchange k v s, DownIntro k v s, Neg a)
  => Down a < _Γ -|s|- _Δ
  -- --------------------
  ->      a < _Γ -|s|- _Δ
downL' p = downR init >>> wkL' p

downR'
  :: (Weaken k v s, Exchange k v s, DownIntro k v s, Neg a)
  => _Γ -|s|- _Δ > Down a
  -- --------------------
  -> _Γ -|s|- _Δ >      a
downR' p = wkR' p >>> downL init
