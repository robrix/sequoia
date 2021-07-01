{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Multiplicative
( -- * Multiplicative rules
  MultiplicativeIntro
, parLTensor
  -- * Re-exports
, module Focalized.Calculus.Bottom
, module Focalized.Calculus.One
, module Focalized.Calculus.Par
, module Focalized.Calculus.Tensor
) where

import Focalized.Calculus.Bottom
import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Negate
import Focalized.Calculus.One
import Focalized.Calculus.Par
import Focalized.Calculus.Tensor
import Focalized.Polarity
import Prelude hiding (init)

type MultiplicativeIntro s = (BottomIntro s, OneIntro s, ParIntro s, TensorIntro s)


parLTensor
  :: (Weaken s, ParIntro s, TensorIntro s, NegateIntro s, Neg a, Neg b)
  =>         _Γ -|s r|- _Δ > r -a ⊗ r -b
  -> a ⅋ b < _Γ -|s r|- _Δ
parLTensor s = wkL s >>> tensorL (negateL (negateL (parL (wkR init) init)))
