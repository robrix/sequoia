module Focalized.Calculus.Control
( -- * Delimited control
  Control(..)
  -- * Continuations
, kL
, kR
, kL'
, kR'
) where

import Focalized.CPS
import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Prelude hiding (init)

-- Delimited control

class  Control s where
  reset
    :: i -|s o|- o
    -- -----------
    -> i -|s r|- o
  shift
    :: r •a < i -|s r|- o > r
    -- ----------------------
    ->        i -|s r|- o > a


-- Continuations

kL
  :: Contextual s
  =>       i -|s r|- o > a
  -- ----------------------
  -> r •a < i -|s r|- o
kL = popL . pushR

kR
  :: (Contextual s, Weaken s)
  => a < i -|s r|- o
  -- ----------------------
  ->     i -|s r|- o > r •a
kR s = lowerL (pushL init) (wkR s)

kL'
  :: (Contextual s, Weaken s)
  => r •a < i -|s r|- o
  -- ----------------------
  ->        i -|s r|- o > a
kL' s = kR init >>> wkR s

kR'
  :: (Contextual s, Weaken s)
  =>     i -|s r|- o > r •a
  -- ----------------------
  -> a < i -|s r|- o
kR' s = wkL s >>> kL init
