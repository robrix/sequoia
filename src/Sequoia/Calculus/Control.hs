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
import Sequoia.Calculus.Structural
import Sequoia.Contextual
import Sequoia.Functor.K

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
  :: Contextual e r s
  =>         _Γ -|s|- _Δ > a
  -- -----------------------
  -> K r a < _Γ -|s|- _Δ
kL = popL . pushR

kR
  :: (Contextual e r s, Weaken e r s)
  => a < _Γ -|s|- _Δ
  -- -----------------------
  ->     _Γ -|s|- _Δ > K r a
kR s = lowerL (pushL init) (wkR s)

kL'
  :: (Contextual e r s, Weaken e r s)
  => K r a < _Γ -|s|- _Δ
  -- -----------------------
  ->         _Γ -|s|- _Δ > a
kL' s = kR init >>> wkR s

kR'
  :: (Contextual e r s, Weaken e r s)
  =>     _Γ -|s|- _Δ > K r a
  -- -----------------------
  -> a < _Γ -|s|- _Δ
kR' s = wkL s >>> kL init
