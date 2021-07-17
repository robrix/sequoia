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

type NegationIntro s = (NotIntro s, NegateIntro s)


-- Negative double negation

dneN
  :: (NegationIntro s, Neg a)
  =>     a < _Γ -|s e r|- _Δ
  -- -----------------------
  -> r ¬-a < _Γ -|s e r|- _Δ
dneN = notL . negateR

dniN
  :: (NegationIntro s, Neg a)
  => _Γ -|s e r|- _Δ > a
  -- -----------------------
  -> _Γ -|s e r|- _Δ > r ¬-a
dniN = notR . negateL


-- Positive double negation

dneP
  :: (NegationIntro s, Pos a)
  =>     a < _Γ -|s e r|- _Δ
  -- -----------------------
  -> r -¬a < _Γ -|s e r|- _Δ
dneP = negateL . notR

dniP
  :: (NegationIntro s, Pos a)
  => _Γ -|s e r|- _Δ > a
  -- -----------------------
  -> _Γ -|s e r|- _Δ > r -¬a
dniP = negateR . notL
