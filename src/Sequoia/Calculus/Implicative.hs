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
import Sequoia.Calculus.Subtraction
import Sequoia.Polarity

type ImplicativeIntro r e s = (FunctionIntro r e s, SubtractionIntro r e s)

funLSub
  :: (Weaken r e s, Exchange r e s, FunctionIntro r e s, SubtractionIntro r e s, Pos a, Neg b)
  =>             _Γ -|s|- _Δ > a ~-r-< b
  -- -----------------------------------
  -> a ~~Fun r e~> b < _Γ -|s|- _Δ
funLSub s = wkL s >>> subL (exL (funL init init))

subLFun
  :: (Weaken r e s, Exchange r e s, FunctionIntro r e s, SubtractionIntro r e s, Pos a, Neg b)
  =>             _Γ -|s|- _Δ > a ~~Fun r e~> b
  -- -----------------------------------
  -> a ~-r-< b < _Γ -|s|- _Δ
subLFun s = wkL s >>> funL (subL (wkR init)) (exL (subL (wkL init)))
