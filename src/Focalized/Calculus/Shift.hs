module Focalized.Calculus.Shift
( -- * Negative shift
  NegShift(..)
, upL'
, upR'
  -- * Positive shift
, PosShift(..)
, downL'
, downR'
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Polarity
import Prelude hiding (init)

-- Negative shift

class NegShift s where
  upL
    :: Pos a
    =>    a < i -|s r|- o
    -- ------------------
    -> Up a < i -|s r|- o

  upR
    :: Pos a
    => i -|s r|- o >    a
    -- ------------------
    -> i -|s r|- o > Up a


upL'
  :: (Weaken s, Exchange s, NegShift s, Pos a)
  => Up a < i -|s r|- o
  -- ------------------
  ->    a < i -|s r|- o
upL' p = upR init >>> wkL' p

upR'
  :: (Weaken s, Exchange s, NegShift s, Pos a)
  => i -|s r|- o > Up a
  -- ------------------
  -> i -|s r|- o >    a
upR' p = wkR' p >>> upL init


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
