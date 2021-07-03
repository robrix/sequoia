module Focalized.Calculus.Control
( -- * Delimited control
  Control(..)
  -- * Continuations
, kL
, kR
, kL'
, kR'
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Continuation
import Prelude hiding (init)

-- Delimited control

class  Control s where
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
  :: Contextual s
  =>       _Γ -|s r|- _Δ > a
  -- ------------------------
  -> r •a < _Γ -|s r|- _Δ
kL = popL . pushR

kR
  :: (Contextual s, Weaken s)
  => a < _Γ -|s r|- _Δ
  -- ------------------------
  ->     _Γ -|s r|- _Δ > r •a
kR s = lowerL (pushL init) (wkR s)

kL'
  :: (Contextual s, Weaken s)
  => r •a < _Γ -|s r|- _Δ
  -- ------------------------
  ->        _Γ -|s r|- _Δ > a
kL' s = kR init >>> wkR s

kR'
  :: (Contextual s, Weaken s)
  =>     _Γ -|s r|- _Δ > r •a
  -- ------------------------
  -> a < _Γ -|s r|- _Δ
kR' s = wkL s >>> kL init
