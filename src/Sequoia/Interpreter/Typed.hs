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
, vvar
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
import Sequoia.Connective.Negate
import Sequoia.Connective.Not
import Sequoia.Connective.Par
import Sequoia.Connective.Subtraction
import Sequoia.Connective.Sum
import Sequoia.Connective.Tensor
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
  XParR :: Expr (Either a b) -> Expr (a ⅋ b)
  XTensorR :: Expr a -> Expr b -> Expr (a ⊗ b)
  XNotR :: Coexpr a -> Expr (Not a R)
  XNegR :: Coexpr a -> Expr (Negate E a R)
  XFunR :: Expr b -> Expr (Fun R a b)
  XSubR :: Expr a -> Coexpr b -> Expr (Sub R b a)

deriving instance Show (Expr b)

data Coexpr a where
  XWithL1 :: Coexpr a -> Coexpr (a & b)
  XWithL2 :: Coexpr b -> Coexpr (a & b)
  XSumL :: Coexpr a -> Coexpr b -> Coexpr (a ⊕ b)
  XParL :: Coexpr a -> Coexpr b -> Coexpr (a ⅋ b)
  XTensorL :: Coexpr (a, b) -> Coexpr (a ⊗ b)
  XNotL :: Expr a -> Coexpr (Not a R)
  XNegL :: Expr a -> Coexpr (Negate E a R)
  XFunL :: Expr a -> Coexpr b -> Coexpr (Fun R a b)
  XSubL :: Expr b -> Coexpr (Sub R b a)

deriving instance Show (Coexpr a)


-- Values

data Val b where
  VNe :: Lv a -> Val a
  VWithR :: Val a -> Val b -> Val (a & b)
  VSumR1 :: Val a -> Val (a ⊕ b)
  VSumR2 :: Val b -> Val (a ⊕ b)
  VParR :: Val (Either a b) -> Val (a ⅋ b)
  VTensorR :: Val a -> Val b -> Val (a ⊗ b)
  VNotR :: Coval a -> Val (Not a R)
  VNegR :: Coval a -> Val (Negate E a R)
  VFunR :: (Val a -> Val b) -> Val (Fun R a b)
  VSubR :: Val a -> Coval b -> Val (Sub R b a)

vvar :: Lv a -> Val a
vvar = VNe

data Coval a where
  VWithL1 :: Coval a -> Coval (a & b)
  VWithL2 :: Coval b -> Coval (a & b)
  VSumL :: Coval a -> Coval b -> Coval (a ⊕ b)
  VParL :: Coval a -> Coval b -> Coval (a ⅋ b)
  VTensorL :: Coval (a, b) -> Coval (a ⊗ b)
  VNotL :: Val a -> Coval (Not a R)
  VNegL :: Val a -> Coval (Negate E a R)
  VFunL :: Val a -> Coval b -> Coval (Fun R a b)
  VSubL :: (Val a -> Val b) -> Coval (Sub R b a)


-- Quotation

quoteVal :: Cardinal -> Val b -> Expr b
quoteVal c = \case
  VNe l        -> XVar (lvToIx c l)
  VWithR a b   -> XWithR (quoteVal c a) (quoteVal c b)
  VSumR1 a     -> XSumR1 (quoteVal c a)
  VSumR2 b     -> XSumR2 (quoteVal c b)
  VParR a      -> XParR (quoteVal c a)
  VTensorR a b -> XTensorR (quoteVal c a) (quoteVal c b)
  VNotR a      -> XNotR (quoteCoval c a)
  VNegR a      -> XNegR (quoteCoval c a)
  VFunR f      -> XFunR (quoteBinder c f)
  VSubR a b    -> XSubR (quoteVal c a) (quoteCoval c b)

quoteCoval :: Cardinal -> Coval a -> Coexpr a
quoteCoval c = \case
  VWithL1 f  -> XWithL1 (quoteCoval c f)
  VWithL2 g  -> XWithL2 (quoteCoval c g)
  VSumL f g  -> XSumL (quoteCoval c f) (quoteCoval c g)
  VParL f g  -> XParL (quoteCoval c f) (quoteCoval c g)
  VTensorL f -> XTensorL (quoteCoval c f)
  VNotL a    -> XNotL (quoteVal c a)
  VNegL a    -> XNegL (quoteVal c a)
  VFunL a b  -> XFunL (quoteVal c a) (quoteCoval c b)
  VSubL f    -> XSubL (quoteBinder c f)

quoteBinder :: Cardinal -> (Val a -> Val b) -> Expr b
quoteBinder c f = quoteVal (succ c) (f (vvar (Lv c)))


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
  XVar i       -> i <! ctx
  XWithR a b   -> VWithR (evalDef ctx a) (evalDef ctx b)
  XSumR1 a     -> VSumR1 (evalDef ctx a)
  XSumR2 b     -> VSumR2 (evalDef ctx b)
  XParR a      -> VParR (evalDef ctx a)
  XTensorR a b -> VTensorR (evalDef ctx a) (evalDef ctx b)
  XNotR a      -> VNotR (coevalDef ctx a)
  XNegR a      -> VNegR (coevalDef ctx a)
  XFunR f      -> VFunR (evalBinder ctx f)
  XSubR a b    -> VSubR (evalDef ctx a) (coevalDef ctx b)

coevalDef :: Γ Val as -> Coexpr b -> Coval b
coevalDef ctx = \case
  XWithL1 f  -> VWithL1 (coevalDef ctx f)
  XWithL2 g  -> VWithL2 (coevalDef ctx g)
  XSumL f g  -> VSumL (coevalDef ctx f) (coevalDef ctx g)
  XParL f g  -> VParL (coevalDef ctx f) (coevalDef ctx g)
  XTensorL f -> VTensorL (coevalDef ctx f)
  XNotL a    -> VNotL (evalDef ctx a)
  XNegL a    -> VNegL (evalDef ctx a)
  XFunL a b  -> VFunL (evalDef ctx a) (coevalDef ctx b)
  XSubL f    -> VSubL (evalBinder ctx f)

evalBinder :: Γ Val as -> Expr b -> (Val a -> Val b)
evalBinder ctx f a = evalDef (a :< ctx) f


-- Execution

execVal :: Γ I as -> Val b -> Eval R b
execVal ctx = \case
  VNe l        -> pure (getI (lvToIx (cardinality ctx) l <! ctx))
  VWithR a b   -> liftA2 inlr (execVal ctx a) (execVal ctx b)
  VSumR1 a     -> inlF (execVal ctx a)
  VSumR2 b     -> inrF (execVal ctx b)
  VParR a      -> coerceDisj <$> execVal ctx a
  VTensorR a b -> liftA2 inlr (execVal ctx a) (execVal ctx b)
  VNotR a      -> Eval (inK (• coerceK (coeval (execCoval ctx a))))
  VNegR a      -> Eval (inK (• Negate E (coeval (execCoval ctx a))))
  VFunR f      -> pure (fun (\ b a -> let ctx' = I a :< ctx in eval (execVal ctx' (f (vvar (lv ctx')))) • Coeval b))
  VSubR a b    -> do { a' <- execVal ctx a ; pure (coeval (execCoval ctx b) :>- a') }

execCoval :: Γ I as -> Coval a -> Coeval a R
execCoval ctx = \case
  VWithL1 f  -> exlL (execCoval ctx f)
  VWithL2 g  -> exrL (execCoval ctx g)
  VSumL f g  -> execCoval ctx f <••> execCoval ctx g
  VParL f g  -> execCoval ctx f <••> execCoval ctx g
  VTensorL f -> execCoval ctx f <<^ coerceConj
  VNotL a    -> inK (\ x -> eval (execVal ctx a) • coerceK x)
  VNegL a    -> inK (\ x -> eval (execVal ctx a) • coerceK x)
  VFunL a b  -> inK (\ f -> eval (execVal ctx a >>= evalFun f) • execCoval ctx b)
  VSubL f    -> inK (\ (b :>- a) -> let ctx' = I a :< ctx in eval (execVal ctx' (f (vvar (lv ctx')))) • Coeval b)


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
