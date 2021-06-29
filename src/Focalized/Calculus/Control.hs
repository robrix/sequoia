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

class Control s where
  reset
    :: _Γ -|s _Δ|- _Δ
    -- --------------
    -> _Γ -|s r |- _Δ
  shift
    :: r •a < _Γ -|s r|- _Δ > r
    -- ------------------------
    ->        _Γ -|s r|- _Δ > a


-- Continuations

kL
  :: Contextual r s
  =>        _Γ -|s|- _Δ > a
  -- ----------------------
  -> r •a < _Γ -|s|- _Δ
kL = popL . pushR

kR
  :: (Contextual r s, Weaken s)
  => a < _Γ -|s|- _Δ
  -- ----------------------
  ->     _Γ -|s|- _Δ > r •a
kR s = lowerL (pushL init) (wkR s)

kL'
  :: (Contextual r s, Weaken s)
  => r •a < _Γ -|s|- _Δ
  -- ----------------------
  ->        _Γ -|s|- _Δ > a
kL' s = kR init >>> wkR s

kR'
  :: (Contextual r s, Weaken s)
  =>     _Γ -|s|- _Δ > r •a
  -- ----------------------
  -> a < _Γ -|s|- _Δ
kR' s = wkL s >>> kL init
