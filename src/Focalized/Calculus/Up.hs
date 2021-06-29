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
    =>    a < _Γ -|s|- _Δ
    -- ------------------
    -> Up a < _Γ -|s|- _Δ

  upR
    :: Pos a
    => _Γ -|s|- _Δ >    a
    -- ------------------
    -> _Γ -|s|- _Δ > Up a


upL'
  :: (Weaken s, Exchange s, NegShift s, Pos a)
  => Up a < _Γ -|s|- _Δ
  -- ------------------
  ->    a < _Γ -|s|- _Δ
upL' p = upR init >>> wkL' p

upR'
  :: (Weaken s, Exchange s, NegShift s, Pos a)
  => _Γ -|s|- _Δ > Up a
  -- ------------------
  -> _Γ -|s|- _Δ >    a
upR' p = wkR' p >>> upL init
