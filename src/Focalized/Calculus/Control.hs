{-# LANGUAGE TypeFamilies #-}
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

class Control s where
  reset
    :: (Continuation j, Continuation k, R j ~ _Δ)
    => _Γ -|s j|- _Δ
    -- -------------
    -> _Γ -|s k|- _Δ

  shift
    :: Continuation k
    => k a < _Γ -|s k|- _Δ > R k
    -- -------------------------
    ->       _Γ -|s k|- _Δ > a


-- Continuations

kL
  :: Contextual s
  =>         _Γ -|s|- _Δ > a
  -- -----------------------
  -> K s a < _Γ -|s|- _Δ
kL = popL . pushR

kR
  :: (Contextual s, Weaken s)
  => a < _Γ -|s|- _Δ
  -- -----------------------
  ->     _Γ -|s|- _Δ > K s a
kR s = lowerL (pushL init) (wkR s)

kL'
  :: (Contextual s, Weaken s)
  => K s a < _Γ -|s|- _Δ
  -- -----------------------
  ->         _Γ -|s|- _Δ > a
kL' s = kR init >>> wkR s

kR'
  :: (Contextual s, Weaken s)
  =>     _Γ -|s|- _Δ > K s a
  -- -----------------------
  -> a < _Γ -|s|- _Δ
kR' s = wkL s >>> kL init
