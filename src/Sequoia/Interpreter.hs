-- | Direct-style and CPS interpreters for a small polarized calculus.
module Sequoia.Interpreter
( -- * Expressions
  Expr(..)
, Scope(..)
) where

import Sequoia.DeBruijn

-- Expressions

data Expr
  = Var Index
  | RTop
  -- No rule for RZero
  | RBottom
  | ROne
  | RWith Expr Expr
  | RSum1 Expr
  | RSum2 Expr
  | RNot Scope
  -- No rule for LTop
  | LZero
  | LBottom
  | LOne
  | LWith1 Expr Scope
  | LWith2 Expr Scope
  | LSum Expr Scope Scope
  | LNot Expr Expr

newtype Scope = Scope { getScope :: Expr }
