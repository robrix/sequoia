module Sequoia.Calculus.Control
( -- * Values
  vL
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
import Data.Functor.Contravariant
import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Contextual
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Functor.Value

-- Values

vL
  :: Contextual s
  =>     a < _Γ -|s e r|- _Δ
  -- -----------------------
  -> V e a < _Γ -|s e r|- _Δ
vL = mapL join

vR
  :: Contextual s
  => _Γ -|s e r|- _Δ >     a
  -- -----------------------
  -> _Γ -|s e r|- _Δ > V e a
-- FIXME: this should preserve extant dependency on the env
vR = mapR (contramap inV0)

vL'
  :: (Contextual s, Exchange s, Weaken s)
  => V e a < _Γ -|s e r|- _Δ
  -- -----------------------
  ->     a < _Γ -|s e r|- _Δ
vL' s = vR init >>> wkL' s

vR'
  :: (Contextual s, Exchange s, Weaken s)
  => _Γ -|s e r|- _Δ > V e a
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
    :: K r a < _Γ -|s e r|- _Δ > r
    -- ---------------------------
    ->         _Γ -|s e r|- _Δ > a


-- Continuations

kL
  :: Contextual s
  =>         _Γ -|s e r|- _Δ > a
  -- ---------------------------
  -> K r a < _Γ -|s e r|- _Δ
kL = popL . val2 . pushR

kR
  :: (Contextual s, Weaken s)
  => a < _Γ -|s e r|- _Δ
  -- ---------------------------
  ->     _Γ -|s e r|- _Δ > K r a
kR s = lowerL (pushL init . inV0) (wkR s)

kL'
  :: (Contextual s, Weaken s)
  => K r a < _Γ -|s e r|- _Δ
  -- ---------------------------
  ->         _Γ -|s e r|- _Δ > a
kL' s = kR init >>> wkR s

kR'
  :: (Contextual s, Weaken s)
  =>     _Γ -|s e r|- _Δ > K r a
  -- ---------------------------
  -> a < _Γ -|s e r|- _Δ
kR' s = wkL s >>> kL init
