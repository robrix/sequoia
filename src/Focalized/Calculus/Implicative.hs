{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Implicative
( -- * Implicative rules
  Implicative
  -- * Re-exports
, module Focalized.Calculus.Function
, module Focalized.Calculus.Subtraction
) where

import Focalized.Calculus.Function
import Focalized.Calculus.Subtraction

type Implicative s = (Function s, Subtraction s)
