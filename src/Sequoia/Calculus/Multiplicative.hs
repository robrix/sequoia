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
import Sequoia.Calculus.Structural
import Sequoia.Calculus.Tensor
import Sequoia.Polarity

type MultiplicativeIntro s = (BottomIntro s, OneIntro s, ParIntro s, TensorIntro s)


parLTensor
  :: (Weaken s, ParIntro s, TensorIntro s, NegateIntro s, Neg a, Neg b)
  =>         _Γ -|s e r|- _Δ > Negate e r a ⊗ Negate e r b
  -- -----------------------------------------------------
  -> a ⅋ b < _Γ -|s e r|- _Δ
parLTensor s = wkL s >>> tensorL (negateL (negateL (parL (wkR init) init)))

tensorLPar
  :: (Weaken s, ParIntro s, TensorIntro s, NotIntro s, Pos a, Pos b)
  =>         _Γ -|s e r|- _Δ > r ¬a ⅋ r ¬b
  -- -------------------------------------
  -> a ⊗ b < _Γ -|s e r|- _Δ
tensorLPar s = wkL s >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
