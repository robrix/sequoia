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
import Focalized.Calculus.Negate
import Focalized.Calculus.Not
import Focalized.Connective.Negation
import Focalized.Polarity
import Prelude hiding (init)

-- Negation

type NegationIntro k s = (NotIntro k s, NegateIntro k s)


-- Negative double negation

dneN
  :: (NegationIntro k s, Neg a)
  =>     a < _Γ -|s|- _Δ
  -- -------------------
  -> k ¬-a < _Γ -|s|- _Δ
dneN = notL . negateR

dniN
  :: (NegationIntro k s, Neg a)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > k ¬-a
dniN = notR . negateL


-- Positive double negation

dneP
  :: (NegationIntro k s, Pos a)
  =>     a < _Γ -|s|- _Δ
  -- -------------------
  -> k -¬a < _Γ -|s|- _Δ
dneP = negateL . notR

dniP
  :: (NegationIntro k s, Pos a)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > k -¬a
dniP = negateR . notL
