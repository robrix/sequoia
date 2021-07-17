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

type AdditiveIntro e r s = (TopIntro e r (s e r), ZeroIntro s, WithIntro s, SumIntro e r (s e r))

withLSum
  :: (Weaken e r (s e r), SumIntro e r (s e r), WithIntro s, NegateIntro e r (s e r), Neg a, Neg b)
  =>         _Γ -|s e r|- _Δ > r -a ⊕ r -b
  -- -------------------------------------
  -> a & b < _Γ -|s e r|- _Δ
withLSum s = wkL s >>> sumL (negateL (withL1 init)) (negateL (withL2 init))

sumLWith
  :: (Weaken e r (s e r), Exchange e r (s e r), SumIntro e r (s e r), WithIntro s, NotIntro e r (s e r), Pos a, Pos b)
  =>         _Γ -|s e r|- _Δ > r ¬a & r ¬b
  -- -------------------------------------
  -> a ⊕ b < _Γ -|s e r|- _Δ
sumLWith s = wkL s >>> exL (sumL (exL (withL1 (notL init))) (exL (withL2 (notL init))))
