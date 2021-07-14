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

type MultiplicativeIntro k v s = (BottomIntro k v s, OneIntro k v s, ParIntro k v s, TensorIntro k v s)


parLTensor
  :: (Weaken k v s, ParIntro k v s, TensorIntro k v s, NegateIntro k v s, Neg a, Neg b)
  =>         _Γ -|s|- _Δ > k -a ⊗ k -b
  -- ---------------------------------
  -> a ⅋ b < _Γ -|s|- _Δ
parLTensor s = wkL s >>> tensorL (negateL (negateL (parL (wkR init) init)))

tensorLPar
  :: (Weaken k v s, ParIntro k v s, TensorIntro k v s, NotIntro k v s, Pos a, Pos b)
  =>         _Γ -|s|- _Δ > k ¬a ⅋ k ¬b
  -- ---------------------------------
  -> a ⊗ b < _Γ -|s|- _Δ
tensorLPar s = wkL s >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
