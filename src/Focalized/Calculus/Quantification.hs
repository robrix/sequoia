{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Quantification
( -- * Quantification rules
  QuantificationIntro
  -- * Re-exports
, module Focalized.Calculus.ForAll
, module Focalized.Calculus.Exists
) where

import Focalized.Calculus.Exists
import Focalized.Calculus.ForAll

-- Quantification rules

type QuantificationIntro s = (UniversalIntro s, ExistentialIntro s)
