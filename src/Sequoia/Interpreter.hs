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
, vapp
  -- ** Elimination
, showsVal
, showsElim
  -- * Quotation
, quoteVal
, quoteElim
) where

import Data.Foldable (foldl')
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
  | LZero Expr
  | LBottom Expr
  | LOne Expr
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

instance Show Val where
  showsPrec = showsVal 0


data Elim
  = EZero
  | EBottom
  | EOne
  | EWith1 (Val -> Val)
  | EWith2 (Val -> Val)
  | ESum (Val -> Val) (Val -> Val)
  | ENot Val
  | ENeg Val

instance Show Elim where
  showsPrec = showsElim 0


-- Construction

vvar :: Level -> Val
vvar d = VNe d Nil

vapp :: Val -> Elim -> Val
vapp = curry $ \case
  (v,         EZero)    -> v
  (VBottom,   EBottom)  -> VBottom
  (VOne,      EOne)     -> VOne
  (VWith a _, EWith1 f) -> f a
  (VWith _ b, EWith2 g) -> g b
  (VSum1 a,   ESum f _) -> f a
  (VSum2 b,   ESum _ g) -> g b
  (VNot k,    ENot a)   -> k a
  (VNeg k,    ENeg a)   -> k a
  (v,        e)         -> error $ "cannot elim " <> show v <> " with " <> show e


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
  EWith1 f -> showsUnaryWith (showsBinder d) "EWith1" p f
  EWith2 g -> showsUnaryWith (showsBinder d) "EWith2" p g
  ESum f g -> showsBinaryWith (showsBinder d) (showsBinder d) "ESum" p f g
  ENot v   -> showsUnaryWith (showsVal d) "ENot" p v
  ENeg v   -> showsUnaryWith (showsVal d) "ENeg" p v

showsBinder :: Level -> Int -> (Val -> Val) -> ShowS
showsBinder d p b = showsVal (succ d) p (b (vvar d))


-- Quotation

quoteVal :: Level -> Val -> Expr
quoteVal d = \case
  VNe v sp  -> foldl' (quoteElim d) (Var (levelToIndex d v)) sp
  VTop      -> RTop
  VBottom   -> RBottom
  VOne      -> ROne
  VWith a b -> RWith (quoteVal d a) (quoteVal d b)
  VSum1 a   -> RSum1 (quoteVal d a)
  VSum2 b   -> RSum2 (quoteVal d b)
  VNot f    -> RNot (quoteBinder d f)
  VNeg f    -> RNeg (quoteBinder d f)

quoteElim :: Level -> Expr -> Elim -> Expr
quoteElim d s = \case
  EZero    -> LZero s
  EBottom  -> LBottom s
  EOne     -> LOne s
  EWith1 f -> LWith1 s (quoteBinder d f)
  EWith2 g -> LWith2 s (quoteBinder d g)
  ESum f g -> LSum s (quoteBinder d f) (quoteBinder d g)
  ENot v   -> LNot s (quoteVal d v)
  ENeg v   -> LNeg s (quoteVal d v)

quoteBinder :: Level -> (Val -> Val) -> Scope
quoteBinder d f = Scope (quoteVal (succ d) (f (vvar d)))
