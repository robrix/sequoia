{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Calculus.Control
( -- * Delimited control
  Control(..)
  -- * Continuations
, kL
, kR
, kL'
, kR'
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Continuation as K

-- Delimited control

class Control k s | s -> k where
  reset
    :: _Γ -|s _Δ e|- _Δ
    -- ----------------
    -> _Γ -|s r  e|- _Δ

  shift
    :: (K.Representable (k r), K.Rep (k r) ~ r)
    => k r a < _Γ -|s r e|- _Δ > r
    -- ---------------------------
    ->         _Γ -|s r e|- _Δ > a


-- Continuations

kL
  :: Contextual k v s
  =>       _Γ -|s|- _Δ > a
  -- ---------------------
  -> k a < _Γ -|s|- _Δ
kL = popL . pushR

kR
  :: (Contextual k v s, Weaken k v s)
  => a < _Γ -|s|- _Δ
  -- ---------------------
  ->     _Γ -|s|- _Δ > k a
kR s = lowerL (pushL init) (wkR s)

kL'
  :: (Contextual k v s, Weaken k v s)
  => k a < _Γ -|s|- _Δ
  -- ---------------------
  ->       _Γ -|s|- _Δ > a
kL' s = kR init >>> wkR s

kR'
  :: (Contextual k v s, Weaken k v s)
  =>     _Γ -|s|- _Δ > k a
  -- ---------------------
  -> a < _Γ -|s|- _Δ
kR' s = wkL s >>> kL init
