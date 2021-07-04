module Sequoia.Calculus.Up
( -- * Up
  UpIntro(..)
, upL'
, upR'
  -- * Connectives
, module Sequoia.Connective.Up
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Up
import Sequoia.Polarity
import Prelude hiding (init)

-- Up

class Core k s => UpIntro k s where
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
  :: (Weaken k s, Exchange k s, UpIntro k s, Pos a)
  => Up a < _Γ -|s|- _Δ
  -- ------------------
  ->    a < _Γ -|s|- _Δ
upL' p = upR init >>> wkL' p

upR'
  :: (Weaken k s, Exchange k s, UpIntro k s, Pos a)
  => _Γ -|s|- _Δ > Up a
  -- ------------------
  -> _Γ -|s|- _Δ >    a
upR' p = wkR' p >>> upL init
