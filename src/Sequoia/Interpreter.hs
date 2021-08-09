-- | Direct-style and CPS interpreters for a small polarized calculus.
module Sequoia.Interpreter
( -- * Expressions
  Expr(..)
, Scope(..)
  -- * Values
, Val(..)
, Elim(..)
) where

import Sequoia.DeBruijn
import Sequoia.Snoc

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
  | RNeg Scope
  -- No rule for LTop
  | LZero
  | LBottom
  | LOne
  | LWith1 Expr Scope
  | LWith2 Expr Scope
  | LSum Expr Scope Scope
  | LNot Expr Expr
  | LNeg Expr Expr
  deriving (Show)

newtype Scope = Scope { getScope :: Expr }
  deriving (Show)


-- Values

data Val
  = VNe Level (Snoc Elim)
  | VTop
  | VBottom
  | VOne
  | VWith Val Val
  | VSum1 Val
  | VSum2 Val
  | VNot (Val -> Val)
  | VNeg (Val -> Val)

data Elim
  = EZero
  | EBottom
  | EOne
  | EWIth1 (Val -> Val)
  | EWIth2 (Val -> Val)
  | ESum (Val -> Val) (Val -> Val)
  | ENot Val
  | ENeg Val
