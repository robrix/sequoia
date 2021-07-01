{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Implicative
( -- * Implicative rules
  ImplicativeIntro
  -- * Re-exports
, module Focalized.Calculus.Function
, module Focalized.Calculus.Subtraction
) where

import Focalized.Calculus.Function
import Focalized.Calculus.Subtraction

type ImplicativeIntro s = (FunctionIntro s, SubtractionIntro s)
