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

import Control.Applicative (liftA2)
import Prelude hiding (exp)
import Sequoia.Conjunction
import Sequoia.Connective.Function
import Sequoia.Connective.Sum
import Sequoia.Connective.With
import Sequoia.Disjunction
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
  XWithR :: Expr a -> Expr b -> Expr (a & b)
  XSumR1 :: Expr a -> Expr (a ⊕ b)
  XSumR2 :: Expr b -> Expr (a ⊕ b)
  XFunR :: Expr b -> Expr (Fun R a b)

deriving instance Show (Expr b)

data Coexpr a where
  XWithL1 :: Coexpr a -> Coexpr (a & b)
  XWithL2 :: Coexpr b -> Coexpr (a & b)
  XSumL :: Coexpr a -> Coexpr b -> Coexpr (a ⊕ b)
  XFunL :: Expr a -> Coexpr b -> Coexpr (Fun R a b)

deriving instance Show (Coexpr a)


-- Values

data Val b where
  VNe :: Lv a -> Val a
  VWithR :: Val a -> Val b -> Val (a & b)
  VSumR1 :: Val a -> Val (a ⊕ b)
  VSumR2 :: Val b -> Val (a ⊕ b)
  VFunR :: (Val a -> Val b) -> Val (Fun R a b)

data Coval a where
  VWithL1 :: Coval a -> Coval (a & b)
  VWithL2 :: Coval b -> Coval (a & b)
  VSumL :: Coval a -> Coval b -> Coval (a ⊕ b)
  VFunL :: Val a -> Coval b -> Coval (Fun R a b)


-- Quotation

quoteVal :: Cardinal -> Val b -> Expr b
quoteVal c = \case
  VNe l      -> XVar (lvToIx c l)
  VWithR a b -> XWithR (quoteVal c a) (quoteVal c b)
  VSumR1 a   -> XSumR1 (quoteVal c a)
  VSumR2 b   -> XSumR2 (quoteVal c b)
  VFunR f    -> XFunR (quoteVal (succ c) (f (VNe (Lv c))))

quoteCoval :: Cardinal -> Coval a -> Coexpr a
quoteCoval c = \case
  VWithL1 f -> XWithL1 (quoteCoval c f)
  VWithL2 g -> XWithL2 (quoteCoval c g)
  VSumL f g -> XSumL (quoteCoval c f) (quoteCoval c g)
  VFunL a b -> XFunL (quoteVal c a) (quoteCoval c b)


-- Evaluator

evalFun :: Fun r a b -> a -> Eval r b
evalFun f a = Eval (K (\ k -> getFun f (coeval k) • a))

newtype Eval r a = Eval { eval :: Coeval a r • r }
  deriving (Applicative, Functor, Monad, MonadRunK r) via DN r

newtype Coeval a r = Coeval { coeval :: a • r }
  deriving (Continuation, ContinuationE, ContinuationI, Profunctor)


-- Definitional interpreter

evalDef :: Γ Val as -> Expr b -> Val b
evalDef ctx = \case
  XVar i     -> i <! ctx
  XWithR a b -> VWithR (evalDef ctx a) (evalDef ctx b)
  XSumR1 a   -> VSumR1 (evalDef ctx a)
  XSumR2 b   -> VSumR2 (evalDef ctx b)
  XFunR f    -> VFunR (\ a -> evalDef (a :< ctx) f)

coevalDef :: Γ Val as -> Coexpr b -> Coval b
coevalDef ctx = \case
  XWithL1 f -> VWithL1 (coevalDef ctx f)
  XWithL2 g -> VWithL2 (coevalDef ctx g)
  XSumL f g -> VSumL (coevalDef ctx f) (coevalDef ctx g)
  XFunL a b -> VFunL (evalDef ctx a) (coevalDef ctx b)


-- Execution

execVal :: Γ I as -> Val b -> Eval R b
execVal ctx = \case
  VNe l      -> pure (getI (lvToIx (cardinality ctx) l <! ctx))
  VWithR a b -> liftA2 inlr (execVal ctx a) (execVal ctx b)
  VSumR1 a   -> inlF (execVal ctx a)
  VSumR2 b   -> inrF (execVal ctx b)
  VFunR f    -> pure (fun (\ b a -> let ctx' = I a :< ctx in eval (execVal ctx' (f (VNe (lv ctx')))) • Coeval b))

execCoval :: Γ I as -> Coval a -> Coeval a R
execCoval ctx = \case
  VWithL1 f -> exlL (execCoval ctx f)
  VWithL2 g -> exrL (execCoval ctx g)
  VSumL f g -> execCoval ctx f <••> execCoval ctx g
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
