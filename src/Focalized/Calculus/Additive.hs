{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Additive
( -- * Additive rules
  AdditiveIntro
, withLSum
  -- * Re-exports
, module Focalized.Calculus.Top
, module Focalized.Calculus.Zero
, module Focalized.Calculus.With
, module Focalized.Calculus.Sum
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Negate
import Focalized.Calculus.Sum
import Focalized.Calculus.Top
import Focalized.Calculus.With
import Focalized.Calculus.Zero
import Focalized.Polarity
import Prelude hiding (init)

type AdditiveIntro s = (TopIntro s, ZeroIntro s, WithIntro s, SumIntro s)

withLSum
  :: (Weaken s, SumIntro s, WithIntro s, NegateIntro s, Neg a, Neg b)
  =>         _Γ -|s r|- _Δ > r -a ⊕ r -b
  -> a & b < _Γ -|s r|- _Δ
withLSum s = wkL s >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
