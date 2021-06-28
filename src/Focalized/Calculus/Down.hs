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
    =>      a < i -|s r|- o
    -- --------------------
    -> Down a < i -|s r|- o

  downR
    :: Neg a
    => i -|s r|- o >      a
    -- --------------------
    -> i -|s r|- o > Down a


downL'
  :: (Weaken s, Exchange s, PosShift s, Neg a)
  => Down a < i -|s r|- o
  -- --------------------
  ->      a < i -|s r|- o
downL' p = downR init >>> wkL' p

downR'
  :: (Weaken s, Exchange s, PosShift s, Neg a)
  => i -|s r|- o > Down a
  -- --------------------
  -> i -|s r|- o >      a
downR' p = wkR' p >>> downL init
