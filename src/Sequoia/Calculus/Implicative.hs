{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Implicative
( -- * Implicative rules
  ImplicativeIntro
, funLSub
, subLFun
  -- * Re-exports
, module Sequoia.Calculus.Function
, module Sequoia.Calculus.Subtraction
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Function
import Sequoia.Calculus.Structural
import Sequoia.Calculus.Subtraction
import Sequoia.Polarity

type ImplicativeIntro s = (FunctionIntro s, SubtractionIntro s)

funLSub
  :: (Weaken s, Exchange s, FunctionIntro s, SubtractionIntro s, Pos a, Neg b)
  =>                 _Γ -|s e r|- _Δ > b >-Sub e r-~ a
  -- -------------------------------------------------
  -> a ~~Fun r~> b < _Γ -|s e r|- _Δ
funLSub s = wkL s >>> subL (exL (init ->⊢ init))

subLFun
  :: (Weaken s, Exchange s, FunctionIntro s, SubtractionIntro s, Pos a, Neg b)
  =>                   _Γ -|s e r|- _Δ > a ~~Fun r~> b
  -- -------------------------------------------------
  -> b >-Sub e r-~ a < _Γ -|s e r|- _Δ
subLFun s = wkL s >>> subL (wkR init) ->⊢ exL (subL (wkL init))
