{-# LANGUAGE GADTs #-}
module Sequoia.Interpreter.Typed
( -- * Expressions
  Expr(..)
, Coexpr(..)
, Scope(..)
) where

import Data.Void
import Sequoia.DeBruijn

-- Expressions

data Expr a where
  Var :: Index -> Expr a
  RBot :: Expr _Δ -> Expr Void
  ROne :: Expr ()
  RFun :: Scope a b -> Expr (a -> b)

deriving instance Show (Expr a)

data Coexpr a where
  Covar :: Index -> Coexpr a
  LBot :: Coexpr Void
  LOne :: Coexpr _Γ -> Coexpr ()
  LFun :: Expr a -> Coexpr b -> Coexpr (a -> b)

newtype Scope a b = Scope { getScope :: Expr b }
  deriving (Show)
