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

type MultiplicativeIntro k s = (BottomIntro k s, OneIntro k s, ParIntro k s, TensorIntro k s)


parLTensor
  :: (Weaken k s, ParIntro k s, TensorIntro k s, NegateIntro k s, Neg a, Neg b)
  =>         _Γ -|s|- _Δ > k -a ⊗ k -b
  -- ---------------------------------
  -> a ⅋ b < _Γ -|s|- _Δ
parLTensor s = wkL s >>> tensorL (negateL (negateL (parL (wkR init) init)))

tensorLPar
  :: (Weaken k s, ParIntro k s, TensorIntro k s, NotIntro k s, Pos a, Pos b)
  =>         _Γ -|s|- _Δ > k ¬a ⅋ k ¬b
  -- ---------------------------------
  -> a ⊗ b < _Γ -|s|- _Δ
tensorLPar s = wkL s >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
