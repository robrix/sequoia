module Focalized.Calculus.Up
( -- * Negative shift
  NegShift(..)
, upL'
, upR'
  -- * Connectives
, module Focalized.Up
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Polarity
import Focalized.Up
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
