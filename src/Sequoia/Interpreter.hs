-- | Direct-style and CPS interpreters for a small polarized calculus.
module Sequoia.Interpreter
( -- * Expressions
  Expr(..)
, Scope(..)
  -- * Values
, Val(..)
, Elim(..)
  -- ** Construction
, vvar
  -- ** Elimination
, showsVal
, showsElim
) where

import Data.Functor.Classes
import Sequoia.DeBruijn
import Sequoia.Snoc
import Text.Show (showListWith)

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


-- Construction

vvar :: Level -> Val
vvar d = VNe d Nil


-- Elimination

showsVal :: Level -> Int -> Val -> ShowS
showsVal d p = \case
  VNe v sp  -> showsBinaryWith showsPrec (liftShowsPrec (showsElim d) (showListWith (showsElim d 0))) "VNe" p v sp
  VTop      -> showString "VTop"
  VBottom   -> showString "VBottom"
  VOne      -> showString "VOne"
  VWith a b -> showsBinaryWith (showsVal d) (showsVal d) "VWith" p a b
  VSum1 a   -> showsUnaryWith (showsVal d) "VSum1" p a
  VSum2 b   -> showsUnaryWith (showsVal d) "VSum2" p b
  VNot a    -> showsUnaryWith (showsBinder d) "VNot" p a
  VNeg a    -> showsUnaryWith (showsBinder d) "VNeg" p a

showsElim :: Level -> Int -> Elim -> ShowS
showsElim d p = \case
  EZero    -> showString "EZero"
  EBottom  -> showString "EBottom"
  EOne     -> showString "EOne"
  EWIth1 f -> showsUnaryWith (showsBinder d) "EWith1" p f
  EWIth2 g -> showsUnaryWith (showsBinder d) "EWith2" p g
  ESum f g -> showsBinaryWith (showsBinder d) (showsBinder d) "ESum" p f g
  ENot v   -> showsUnaryWith (showsVal d) "ENot" p v
  ENeg v   -> showsUnaryWith (showsVal d) "ENeg" p v

showsBinder :: Level -> Int -> (Val -> Val) -> ShowS
showsBinder d p b = showsVal (succ d) p (b (vvar d))
