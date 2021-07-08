{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Multiplicative
( -- * Multiplicative rules
  MultiplicativeIntro
, parLTensor
, tensorLPar
  -- * Re-exports
, module Sequoia.Calculus.Bottom
, module Sequoia.Calculus.One
, module Sequoia.Calculus.Par
, module Sequoia.Calculus.Tensor
) where

import Prelude hiding (init)
import Sequoia.Calculus.Bottom
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Negation
import Sequoia.Calculus.One
import Sequoia.Calculus.Par
import Sequoia.Calculus.Tensor
import Sequoia.Polarity

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
