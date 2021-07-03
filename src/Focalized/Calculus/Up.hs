module Focalized.Calculus.Up
( -- * Up
  UpIntro(..)
, upL'
, upR'
  -- * Connectives
, module Focalized.Connective.Up
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Up
import Focalized.Polarity
import Prelude hiding (init)

-- Up

class Core s => UpIntro s where
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
  :: (Weaken s, Exchange s, UpIntro s, Pos a)
  => Up a < _Γ -|s|- _Δ
  -- ------------------
  ->    a < _Γ -|s|- _Δ
upL' p = upR init >>> wkL' p

upR'
  :: (Weaken s, Exchange s, UpIntro s, Pos a)
  => _Γ -|s|- _Δ > Up a
  -- ------------------
  -> _Γ -|s|- _Δ >    a
upR' p = wkR' p >>> upL init
