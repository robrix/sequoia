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

type Negation s = (NegNegation s, PosNegation s)


-- Negative double negation

dneN
  :: (NegNegation s, PosNegation s, Neg a)
  =>     a < _Γ -|s r|- _Δ
  -- ---------------------
  -> r ¬-a < _Γ -|s r|- _Δ
dneN = notL . negateR

dniN
  :: (NegNegation s, PosNegation s, Neg a)
  => _Γ -|s r|- _Δ > a
  -- ---------------------
  -> _Γ -|s r|- _Δ > r ¬-a
dniN = notR . negateL


-- Positive double negation

dneP
  :: (NegNegation s, PosNegation s, Pos a)
  =>     a < _Γ -|s r|- _Δ
  -- ---------------------
  -> r -¬a < _Γ -|s r|- _Δ
dneP = negateL . notR

dniP
  :: (NegNegation s, PosNegation s, Pos a)
  => _Γ -|s r|- _Δ > a
  -- ---------------------
  -> _Γ -|s r|- _Δ > r -¬a
dniP = negateR . notL
