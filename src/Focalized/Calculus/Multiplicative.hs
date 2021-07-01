{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Multiplicative
( -- * Multiplicative rules
  MultiplicativeIntro
  -- * Re-exports
, module Focalized.Calculus.Bottom
, module Focalized.Calculus.One
, module Focalized.Calculus.Par
, module Focalized.Calculus.Tensor
) where

import Focalized.Calculus.Bottom
import Focalized.Calculus.One
import Focalized.Calculus.Par
import Focalized.Calculus.Tensor

type MultiplicativeIntro s = (BottomIntro s, OneIntro s, ParIntro s, TensorIntro s)
