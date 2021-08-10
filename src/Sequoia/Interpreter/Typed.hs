{-# LANGUAGE GADTs #-}
module Sequoia.Interpreter.Typed
( -- Expressions
  Expr(..)
, Scope(..)
) where

import Sequoia.DeBruijn

-- Expressions

data Expr _Γ _Δ where
  Var :: Index -> Expr _Γ (_Δ, b)
  Covar :: Index -> Expr (a, _Γ) _Δ
  RFun :: Scope (a, _Γ) (_Δ, b) -> Expr _Γ (_Δ, a -> b)
  LFun :: Expr _Γ (_Δ, a) -> Expr (b, _Γ) _Δ -> Expr _Γ _Δ

deriving instance Show (Expr _Γ _Δ)

newtype Scope _Γ _Δ = Scope { getScope :: Expr _Γ _Δ }
  deriving (Show)
