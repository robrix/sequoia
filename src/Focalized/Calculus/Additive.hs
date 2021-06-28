{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Additive
( -- * Additive rules
  Additive
  -- * Re-exports
, module Focalized.Calculus.Top
, module Focalized.Calculus.Zero
, module Focalized.Calculus.With
, module Focalized.Calculus.Sum
) where

import Focalized.Calculus.Sum
import Focalized.Calculus.Top
import Focalized.Calculus.With
import Focalized.Calculus.Zero

type Additive s = (NegTruth s, PosFalsity s, NegConjunction s, PosDisjunction s)
