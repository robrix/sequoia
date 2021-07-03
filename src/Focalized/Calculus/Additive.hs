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
import Focalized.Polarity
import Prelude hiding (init)

type AdditiveIntro k s = (TopIntro k s, ZeroIntro k s, WithIntro k s, SumIntro k s)

withLSum
  :: (Weaken k s, SumIntro k s, WithIntro k s, NegateIntro k s, Neg a, Neg b)
  =>         _Γ -|s|- _Δ > k -a ⊕ k -b
  -- ---------------------------------
  -> a & b < _Γ -|s|- _Δ
withLSum s = wkL s >>> sumL (negateL (withL1 init)) (negateL (withL2 init))

sumLWith
  :: (Weaken k s, Exchange k s, SumIntro k s, WithIntro k s, NotIntro k s, Pos a, Pos b)
  =>         _Γ -|s|- _Δ > k ¬a & k ¬b
  -- ---------------------------------
  -> a ⊕ b < _Γ -|s|- _Δ
sumLWith s = wkL s >>> exL (sumL (exL (withL1 (notL init))) (exL (withL2 (notL init))))
