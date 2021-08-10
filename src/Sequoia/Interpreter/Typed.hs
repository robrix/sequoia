{-# LANGUAGE GADTs #-}
module Sequoia.Interpreter.Typed
( -- Expressions
  Expr(..)
, Scope(..)
) where

import Data.Void
import Sequoia.DeBruijn

-- Expressions

data Expr _Γ _Δ where
  Var :: Index -> Expr _Γ (_Δ, b)
  Covar :: Index -> Expr (a, _Γ) _Δ
  LBot :: Expr (Void, _Γ) _Δ
  RBot :: Expr _Γ (_Δ, Void) -> Expr _Γ _Δ
  LOne :: Expr ((), _Γ) _Δ -> Expr _Γ _Δ
  ROne :: Expr _Γ (_Δ, ())
  LFun :: Expr _Γ (_Δ, a) -> Expr (b, _Γ) _Δ -> Expr _Γ _Δ
  RFun :: Scope (a, _Γ) (_Δ, b) -> Expr _Γ (_Δ, a -> b)

deriving instance Show (Expr _Γ _Δ)

newtype Scope _Γ _Δ = Scope { getScope :: Expr _Γ _Δ }
  deriving (Show)
