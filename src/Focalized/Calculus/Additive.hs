{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Additive
( -- * Additive rules
  AdditiveIntro
, withLSum
, sumLWith
  -- * Re-exports
, module Focalized.Calculus.Top
, module Focalized.Calculus.Zero
, module Focalized.Calculus.With
, module Focalized.Calculus.Sum
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Negation
import Focalized.Calculus.Sum
import Focalized.Calculus.Top
import Focalized.Calculus.With
import Focalized.Calculus.Zero
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

type AdditiveIntro s = (TopIntro s, ZeroIntro s, WithIntro s, SumIntro s)

withLSum
  :: (Weaken s, SumIntro s, WithIntro s, NegateIntro s, Neg a, Neg b)
  =>         _Γ -|s|- _Δ > R (K s) -a ⊕ R (K s) -b
  -> a & b < _Γ -|s|- _Δ
withLSum s = wkL s >>> sumL (negateL (withL1 init)) (negateL (withL2 init))

sumLWith
  :: (Weaken s, Exchange s, SumIntro s, WithIntro s, NotIntro s, Pos a, Pos b)
  =>         _Γ -|s|- _Δ > R (K s) ¬a & R (K s) ¬b
  -> a ⊕ b < _Γ -|s|- _Δ
sumLWith s = wkL s >>> exL (sumL (exL (withL1 (notL init))) (exL (withL2 (notL init))))
