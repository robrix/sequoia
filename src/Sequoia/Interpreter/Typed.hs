module Sequoia.Interpreter.Typed
( -- Expressions
  Expr(..)
, Scope(..)
) where

import Sequoia.DeBruijn

-- Expressions

data Expr
  = Var Index
  | RFun Scope
  | LFun Expr Expr
  deriving (Show)

newtype Scope = Scope { getScope :: Expr }
  deriving (Show)
