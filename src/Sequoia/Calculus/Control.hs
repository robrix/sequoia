module Sequoia.Calculus.Control
( -- * Local environments
  Environment(..)
  -- * Values
, vL
, vR
, vL'
, vR'
  -- * Delimited control
, Control(..)
  -- * Continuations
, kL
, kR
, kL'
, kR'
) where

import Control.Monad (join)
import Data.Profunctor
import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Contextual
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Local environments

class Environment s where
  environment
    -- -------------------
    :: _Γ -|s e r|- _Δ > e

  withEnv
    :: _Γ -|s e r|- _Δ > e'   ->   _Γ -|s e' r|- _Δ
    -- --------------------------------------------
    ->               _Γ -|s e r|- _Δ


-- Values

vL
  :: Contextual s
  =>     a < _Γ -|s e r|- _Δ
  -- -----------------------
  -> e ∘ a < _Γ -|s e r|- _Δ
vL = mapL join

vR
  :: Contextual s
  => _Γ -|s e r|- _Δ >     a
  -- -----------------------
  -> _Γ -|s e r|- _Δ > e ∘ a
-- FIXME: this should preserve extant dependency on the env
vR = mapR (lmap pure)

vL'
  :: (Contextual s, Exchange s, Weaken s)
  => e ∘ a < _Γ -|s e r|- _Δ
  -- -----------------------
  ->     a < _Γ -|s e r|- _Δ
vL' s = vR init >>> wkL' s

vR'
  :: (Contextual s, Exchange s, Weaken s)
  => _Γ -|s e r|- _Δ > e ∘ a
  -- -----------------------
  -> _Γ -|s e r|- _Δ >     a
vR' s = wkR' s >>> vL init


-- Delimited control

class Control s where
  reset
    :: _Γ -|s e _Δ|- _Δ
    -- ----------------
    -> _Γ -|s e r |- _Δ

  shift
    :: a • r < _Γ -|s e r|- _Δ > r
    -- ---------------------------
    ->         _Γ -|s e r|- _Δ > a


-- Continuations

kL
  :: Contextual s
  =>         _Γ -|s e r|- _Δ > a
  -- ---------------------------
  -> a • r < _Γ -|s e r|- _Δ
kL = popL . val . pushR

kR
  :: (Contextual s, Weaken s)
  => a < _Γ -|s e r|- _Δ
  -- ---------------------------
  ->     _Γ -|s e r|- _Δ > a • r
kR s = lowerL (pushL init . pure) (wkR s)

kL'
  :: (Contextual s, Weaken s)
  => a • r < _Γ -|s e r|- _Δ
  -- ---------------------------
  ->         _Γ -|s e r|- _Δ > a
kL' s = kR init >>> wkR s

kR'
  :: (Contextual s, Weaken s)
  =>     _Γ -|s e r|- _Δ > a • r
  -- ---------------------------
  -> a < _Γ -|s e r|- _Δ
kR' s = wkL s >>> kL init
