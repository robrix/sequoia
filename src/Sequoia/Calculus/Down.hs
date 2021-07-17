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
import Sequoia.Calculus.Structural
import Sequoia.Connective.Down
import Sequoia.Polarity

-- Down

class Core s => DownIntro s where
  downL
    :: Neg a
    =>      a < _Γ -|s e r|- _Δ
    -- ------------------------
    -> Down a < _Γ -|s e r|- _Δ

  downR
    :: Neg a
    => _Γ -|s e r|- _Δ >      a
    -- ------------------------
    -> _Γ -|s e r|- _Δ > Down a


downL'
  :: (Weaken s, Exchange s, DownIntro s, Neg a)
  => Down a < _Γ -|s e r|- _Δ
  -- ------------------------
  ->      a < _Γ -|s e r|- _Δ
downL' p = downR init >>> wkL' p

downR'
  :: (Weaken s, Exchange s, DownIntro s, Neg a)
  => _Γ -|s e r|- _Δ > Down a
  -- ------------------------
  -> _Γ -|s e r|- _Δ >      a
downR' p = wkR' p >>> downL init
