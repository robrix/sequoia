{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Interpreter.Typed
( -- * Expressions
  E(..)
, R
, absurdR
, Expr(..)
, Coexpr(..)
  -- * Values
, Val(..)
, Coval(..)
  -- * Quotation
, quoteVal
, quoteCoval
  -- * Evaluator
, Eval(..)
, Coeval(..)
  -- * Definitional interpreter
, evalDef
, coevalDef
  -- * Execution
, execVal
, execCoval
  -- * Contexts
, Γ(..)
, (<!)
, cardinality
, lv
, lvToIx
, Lv(level)
, Ix(index)
) where

import Prelude hiding (exp)
import Sequoia.Connective.Function
import Sequoia.Monad.Run
import Sequoia.Profunctor
import Sequoia.Profunctor.Continuation
import Unsafe.Coerce

-- Expressions

data E = E
data R

absurdR :: R -> a
absurdR = \case

data Expr b where
  XVar :: Ix a -> Expr a
  XFunR :: Expr b -> Expr (Fun R a b)

deriving instance Show (Expr b)

data Coexpr a where
  XFunL :: Expr a -> Coexpr b -> Coexpr (Fun R a b)

deriving instance Show (Coexpr a)


-- Values

data Val b where
  VNe :: Lv a -> Val a
  VFunR :: (Val a -> Val b) -> Val (Fun R a b)

data Coval a where
  VFunL :: Val a -> Coval b -> Coval (Fun R a b)


-- Quotation

quoteVal :: Cardinal -> Val b -> Expr b
quoteVal c = \case
  VNe l   -> XVar (lvToIx c l)
  VFunR f -> XFunR (quoteVal (succ c) (f (VNe (Lv c))))

quoteCoval :: Cardinal -> Coval a -> Coexpr a
quoteCoval c = \case
  VFunL a b -> XFunL (quoteVal c a) (quoteCoval c b)


-- Evaluator

evalFun :: Fun r a b -> a -> Eval r b
evalFun f a = Eval (K (\ k -> getFun f (coeval k) • a))

newtype Eval r a = Eval { eval :: Coeval a r • r }
  deriving (Applicative, Functor, Monad, MonadRunK r) via DN r

newtype Coeval a r = Coeval { coeval :: a • r }
  deriving (ContinuationE, ContinuationI, Profunctor)


-- Definitional interpreter

evalDef :: Γ Val as -> Expr b -> Val b
evalDef ctx = \case
  XVar i  -> i <! ctx
  XFunR f -> VFunR (\ a -> evalDef (a :< ctx) f)

coevalDef :: Γ Val as -> Coexpr b -> Coval b
coevalDef ctx = \case
  XFunL a b -> VFunL (evalDef ctx a) (coevalDef ctx b)


-- Execution

execVal :: Γ I as -> Val b -> Eval R b
execVal ctx = \case
  VNe l   -> pure (getI (lvToIx (cardinality ctx) l <! ctx))
  VFunR f -> pure (fun (\ b a -> let ctx' = I a :< ctx in eval (execVal ctx' (f (VNe (lv ctx')))) • Coeval b))

execCoval :: Γ I as -> Coval a -> Coeval a R
execCoval ctx = \case
  VFunL a b -> inK (\ f -> eval (execVal ctx a >>= evalFun f) • execCoval ctx b)


-- Contexts

data Γ f as where
  Γ :: Γ f ()
  (:<) :: f a -> Γ f as -> Γ f (a, as)

infixr 4 :<

(<!) :: Ix a -> Γ f as -> f a
Ix i <! h :< t
  | i == 0    = unsafeCoerce h
  | otherwise = Ix (i - 1) <! t
_    <! Γ     = error "index past end of context"

infixr 2 <!

cardinality :: Γ f as -> Cardinal
cardinality = Cardinal . go 0
  where
  go :: Int -> Γ f as -> Int
  go acc = \case
    Γ       -> acc
    _ :< as -> go (acc + 1) as

newtype Cardinal = Cardinal { getCardinal :: Int }
  deriving (Enum, Eq, Num, Ord, Show)

lv :: Γ f (a, as) -> Lv a
lv = Lv . pred . cardinality

lvToIx :: Cardinal -> Lv a -> Ix a
lvToIx c (Lv l) = Ix (getCardinal (c - l - 1))

newtype Lv a = Lv { level :: Cardinal }
  deriving (Eq, Ord, Show)

newtype Ix a = Ix { index :: Int }
  deriving (Eq, Ord, Show)


newtype I a = I { getI :: a }
  deriving (Eq, Functor, Ord, Show)
