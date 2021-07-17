{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Quantification
( -- * Quantification rules
  QuantificationIntro
  -- * Re-exports
, module Sequoia.Calculus.ForAll
, module Sequoia.Calculus.Exists
) where

import Sequoia.Calculus.Exists
import Sequoia.Calculus.ForAll

-- Quantification rules

type QuantificationIntro s = (UniversalIntro s, ExistentialIntro s)
