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

import           Prelude hiding (init)
import           Sequoia.Calculus.Context
import           Sequoia.Calculus.Core
import           Sequoia.Continuation as K
import qualified Sequoia.Value as V

-- Delimited control

class Control s where
  reset
    :: (K.Representable j, K.Representable k, K.Rep j ~ _Δ, V.Representable v)
    => _Γ -|s j v|- _Δ
    -- ---------------
    -> _Γ -|s k v|- _Δ

  shift
    :: (K.Representable k, V.Representable v)
    => k a < _Γ -|s k v|- _Δ > KRep k
    -- ------------------------------
    ->       _Γ -|s k v|- _Δ > a


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
