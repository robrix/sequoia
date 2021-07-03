{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Negation
( -- * Negation
  NegationIntro
  -- * Re-exports
, module Focalized.Calculus.Not
, module Focalized.Calculus.Negate
, module Focalized.Connective.Negation
  -- * Negative double negation
, dneN
, dniN
  -- * Positive double negation
, dneP
, dniP
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Negate
import Focalized.Calculus.Not
import Focalized.Connective.Negation
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- Negation

type NegationIntro s = (NotIntro s, NegateIntro s)


-- Negative double negation

dneN
  :: (NotIntro s, NegateIntro s, Neg a)
  =>           a < _Γ -|s|- _Δ
  -- -------------------------
  -> R (K s) ¬-a < _Γ -|s|- _Δ
dneN = notL . negateR

dniN
  :: (NotIntro s, NegateIntro s, Neg a)
  => _Γ -|s|- _Δ > a
  -- -------------------------
  -> _Γ -|s|- _Δ > R (K s) ¬-a
dniN = notR . negateL


-- Positive double negation

dneP
  :: (NotIntro s, NegateIntro s, Pos a)
  =>           a < _Γ -|s|- _Δ
  -- -------------------------
  -> R (K s) -¬a < _Γ -|s|- _Δ
dneP = negateL . notR

dniP
  :: (NotIntro s, NegateIntro s, Pos a)
  => _Γ -|s|- _Δ > a
  -- -------------------------
  -> _Γ -|s|- _Δ > R (K s) -¬a
dniP = negateR . notL
