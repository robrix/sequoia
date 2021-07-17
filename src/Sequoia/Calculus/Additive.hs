{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Additive
( -- * Additive rules
  AdditiveIntro
, withLSum
, sumLWith
  -- * Re-exports
, module Sequoia.Calculus.Top
, module Sequoia.Calculus.Zero
, module Sequoia.Calculus.With
, module Sequoia.Calculus.Sum
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Negation
import Sequoia.Calculus.Structural
import Sequoia.Calculus.Sum
import Sequoia.Calculus.Top
import Sequoia.Calculus.With
import Sequoia.Calculus.Zero
import Sequoia.Polarity

type AdditiveIntro s = (TopIntro s, ZeroIntro s, WithIntro s, SumIntro s)

withLSum
  :: (Weaken s, SumIntro s, WithIntro s, NegateIntro s, Neg a, Neg b)
  =>         _Γ -|s e r|- _Δ > r -a ⊕ r -b
  -- -------------------------------------
  -> a & b < _Γ -|s e r|- _Δ
withLSum s = wkL s >>> sumL (negateL (withL1 init)) (negateL (withL2 init))

sumLWith
  :: (Weaken s, Exchange s, SumIntro s, WithIntro s, NotIntro s, Pos a, Pos b)
  =>         _Γ -|s e r|- _Δ > r ¬a & r ¬b
  -- -------------------------------------
  -> a ⊕ b < _Γ -|s e r|- _Δ
sumLWith s = wkL s >>> exL (sumL (exL (withL1 (notL init))) (exL (withL2 (notL init))))
