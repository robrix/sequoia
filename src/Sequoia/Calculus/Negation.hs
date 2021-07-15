{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Negation
( -- * Negation
  NegationIntro
  -- * Re-exports
, module Sequoia.Calculus.Not
, module Sequoia.Calculus.Negate
, module Sequoia.Connective.Negation
  -- * Negative double negation
, dneN
, dniN
  -- * Positive double negation
, dneP
, dniP
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Negate
import Sequoia.Calculus.Not
import Sequoia.Connective.Negation
import Sequoia.Polarity

-- Negation

type NegationIntro e r s = (NotIntro e r s, NegateIntro e r s)


-- Negative double negation

dneN
  :: (NegationIntro e r s, Neg a)
  =>     a < _Γ -|s|- _Δ
  -- -------------------
  -> r ¬-a < _Γ -|s|- _Δ
dneN = notL . negateR

dniN
  :: (NegationIntro e r s, Neg a)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > r ¬-a
dniN = notR . negateL


-- Positive double negation

dneP
  :: (NegationIntro e r s, Pos a)
  =>     a < _Γ -|s|- _Δ
  -- -------------------
  -> r -¬a < _Γ -|s|- _Δ
dneP = negateL . notR

dniP
  :: (NegationIntro e r s, Pos a)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > r -¬a
dniP = negateR . notL
