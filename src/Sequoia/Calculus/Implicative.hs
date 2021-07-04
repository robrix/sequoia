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

type ImplicativeIntro k s = (FunctionIntro k s, SubtractionIntro k s)

funLSub
  :: (Weaken k s, Exchange k s, FunctionIntro k s, SubtractionIntro k s, Pos a, Neg b)
  =>             _Γ -|s|- _Δ > a ~-k-< b
  -- -----------------------------------
  -> a ~~k~> b < _Γ -|s|- _Δ
funLSub s = wkL s >>> subL (exL (funL init init))

subLFun
  :: (Weaken k s, Exchange k s, FunctionIntro k s, SubtractionIntro k s, Pos a, Neg b)
  =>             _Γ -|s|- _Δ > a ~~k~> b
  -- -----------------------------------
  -> a ~-k-< b < _Γ -|s|- _Δ
subLFun s = wkL s >>> funL (subL (wkR init)) (exL (subL (wkL init)))
