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

type ImplicativeIntro e r s = (FunctionIntro e r s, SubtractionIntro e r s)

funLSub
  :: (Weaken e r s, Exchange e r s, FunctionIntro e r s, SubtractionIntro e r s, Pos a, Neg b)
  =>             _Γ -|s|- _Δ > a ~-r-< b
  -- -----------------------------------
  -> a ~~Fun e r~> b < _Γ -|s|- _Δ
funLSub s = wkL s >>> subL (exL (funL init init))

subLFun
  :: (Weaken e r s, Exchange e r s, FunctionIntro e r s, SubtractionIntro e r s, Pos a, Neg b)
  =>             _Γ -|s|- _Δ > a ~~Fun e r~> b
  -- -----------------------------------------
  -> a ~-r-< b < _Γ -|s|- _Δ
subLFun s = wkL s >>> funL (subL (wkR init)) (exL (subL (wkL init)))
