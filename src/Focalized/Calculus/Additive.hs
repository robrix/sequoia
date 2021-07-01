{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Additive
( -- * Additive rules
  AdditiveIntro
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

type AdditiveIntro s = (TopIntro s, ZeroIntro s, WithIntro s, SumIntro s)
