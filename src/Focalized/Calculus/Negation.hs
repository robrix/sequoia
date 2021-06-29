{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Negation
( -- * Negation
  Negation
  -- * Re-exports
, module Focalized.Calculus.Not
, module Focalized.Calculus.Negate
, module Focalized.Negation
  -- * Negative double negation
, dneN
, dniN
  -- * Positive double negation
, dneP
, dniP
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Negate
import Focalized.Calculus.Not
import Focalized.Negation
import Focalized.Polarity
import Prelude hiding (init)

-- Negation

type Negation r s = (NegNegation r s, PosNegation r s)


-- Negative double negation

dneN
  :: (Negation r s, Neg a)
  =>     a < _Γ -|s|- _Δ
  -- -------------------
  -> r ¬-a < _Γ -|s|- _Δ
dneN = notL . negateR

dniN
  :: (Negation r s, Neg a)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > r ¬-a
dniN = notR . negateL


-- Positive double negation

dneP
  :: (Negation r s, Pos a)
  =>     a < _Γ -|s|- _Δ
  -- -------------------
  -> r -¬a < _Γ -|s|- _Δ
dneP = negateL . notR

dniP
  :: (Negation r s, Pos a)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > r -¬a
dniP = negateR . notL
