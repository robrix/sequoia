module Sequoia.Calculus.Up
( -- * Up
  UpIntro(..)
, upL'
, upR'
  -- * Connectives
, module Sequoia.Connective.Up
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Connective.Up
import Sequoia.Polarity

-- Up

class Core s => UpIntro s where
  upL
    :: Pos a
    =>    a < _Γ -|s e r|- _Δ
    -- ----------------------
    -> Up a < _Γ -|s e r|- _Δ

  upR
    :: Pos a
    => _Γ -|s e r|- _Δ >    a
    -- ----------------------
    -> _Γ -|s e r|- _Δ > Up a


upL'
  :: (Weaken s, Exchange s, UpIntro s, Pos a)
  => Up a < _Γ -|s e r|- _Δ
  -- ----------------------
  ->    a < _Γ -|s e r|- _Δ
upL' p = upR init >>> wkL' p

upR'
  :: (Weaken s, Exchange s, UpIntro s, Pos a)
  => _Γ -|s e r|- _Δ > Up a
  -- ----------------------
  -> _Γ -|s e r|- _Δ >    a
upR' p = wkR' p >>> upL init
