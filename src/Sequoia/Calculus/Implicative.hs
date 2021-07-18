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
  =>                   _Γ -|s e r|- _Δ > a ~-Sub e r-< b
  -- ---------------------------------------------------
  -> a ~~Fun e r~> b < _Γ -|s e r|- _Δ
funLSub s = wkL s >>> subL (exL (funL init init))

subLFun
  :: (Weaken s, Exchange s, FunctionIntro s, SubtractionIntro s, Pos a, Neg b)
  =>                   _Γ -|s e r|- _Δ > a ~~Fun e r~> b
  -- ---------------------------------------------------
  -> a ~-Sub e r-< b < _Γ -|s e r|- _Δ
subLFun s = wkL s >>> funL (subL (wkR init)) (exL (subL (wkL init)))
