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

type MultiplicativeIntro e r s = (BottomIntro s, OneIntro e r (s e r), ParIntro e r (s e r), TensorIntro e r (s e r))


parLTensor
  :: (Weaken e r s, ParIntro e r s, TensorIntro e r s, NegateIntro e r s, Neg a, Neg b)
  =>         _Γ -|s|- _Δ > r -a ⊗ r -b
  -- ---------------------------------
  -> a ⅋ b < _Γ -|s|- _Δ
parLTensor s = wkL s >>> tensorL (negateL (negateL (parL (wkR init) init)))

tensorLPar
  :: (Weaken e r s, ParIntro e r s, TensorIntro e r s, NotIntro e r s, Pos a, Pos b)
  =>         _Γ -|s|- _Δ > r ¬a ⅋ r ¬b
  -- ---------------------------------
  -> a ⊗ b < _Γ -|s|- _Δ
tensorLPar s = wkL s >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
