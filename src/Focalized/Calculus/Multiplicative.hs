{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Multiplicative
( -- * Multiplicative rules
  MultiplicativeIntro
, parLTensor
, tensorLPar
  -- * Re-exports
, module Focalized.Calculus.Bottom
, module Focalized.Calculus.One
, module Focalized.Calculus.Par
, module Focalized.Calculus.Tensor
) where

import Focalized.Calculus.Bottom
import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Negation
import Focalized.Calculus.One
import Focalized.Calculus.Par
import Focalized.Calculus.Tensor
import Focalized.Polarity
import Prelude hiding (init)

type MultiplicativeIntro s = (BottomIntro s, OneIntro s, ParIntro s, TensorIntro s)


parLTensor
  :: (Weaken s, ParIntro s, TensorIntro s, NegateIntro s, Neg a, Neg b)
  =>         _Γ -|s|- _Δ > K s -a ⊗ K s -b
  -- -------------------------------------
  -> a ⅋ b < _Γ -|s|- _Δ
parLTensor s = wkL s >>> tensorL (negateL (negateL (parL (wkR init) init)))

tensorLPar
  :: (Weaken s, ParIntro s, TensorIntro s, NotIntro s, Pos a, Pos b)
  =>         _Γ -|s|- _Δ > K s ¬a ⅋ K s ¬b
  -- -------------------------------------
  -> a ⊗ b < _Γ -|s|- _Δ
tensorLPar s = wkL s >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
