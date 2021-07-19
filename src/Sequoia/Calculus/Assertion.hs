{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Assertion
( -- * Assertion
  AssertionIntro
  -- * Re-exports
, module Sequoia.Calculus.NotUntrue
, module Sequoia.Calculus.True
) where

import Sequoia.Calculus.NotUntrue
import Sequoia.Calculus.True

type AssertionIntro s = (NotUntrueIntro s, TrueIntro s)
