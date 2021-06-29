{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Quantification
( -- * Quantification rules
  Quantification
  -- * Re-exports
, module Focalized.Calculus.ForAll
, module Focalized.Calculus.Exists
) where

import Focalized.Calculus.Exists
import Focalized.Calculus.ForAll

-- Quantification rules

type Quantification r s = (Universal r s, Existential r s)
