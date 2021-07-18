{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Assertion
( -- * Assertion
  AssertionIntro
  -- * Re-exports
, module Sequoia.Calculus.True
) where

import Sequoia.Calculus.True

type AssertionIntro s = True s
