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
import Sequoia.Connective.Up
import Sequoia.Polarity

-- Up

class Core k v s => UpIntro k v s where
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
  :: (Weaken k v s, Exchange k v s, UpIntro k v s, Pos a)
  => Up a < _Γ -|s|- _Δ
  -- ------------------
  ->    a < _Γ -|s|- _Δ
upL' p = upR init >>> wkL' p

upR'
  :: (Weaken k v s, Exchange k v s, UpIntro k v s, Pos a)
  => _Γ -|s|- _Δ > Up a
  -- ------------------
  -> _Γ -|s|- _Δ >    a
upR' p = wkR' p >>> upL init
