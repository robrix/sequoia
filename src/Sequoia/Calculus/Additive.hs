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
import Sequoia.Calculus.Sum
import Sequoia.Calculus.Top
import Sequoia.Calculus.With
import Sequoia.Calculus.Zero
import Sequoia.Polarity

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
