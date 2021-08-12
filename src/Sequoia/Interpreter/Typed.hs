{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Interpreter.Typed
( -- * Expressions
  Expr(..)
  -- * Values
, Val(..)
  -- * Quotation
, quoteVal
  -- * Definitional interpreter
, evalDef
  -- * Execution
, execVal
) where

import Control.Applicative (liftA2)
import Control.Category (Category, (>>>))
import Data.Functor ((<&>))
import Prelude hiding (exp)
import Sequoia.Conjunction
import Sequoia.Connective.Bottom
import Sequoia.Connective.Function
import Sequoia.Connective.One
import Sequoia.Connective.Par
import Sequoia.Connective.Subtraction
import Sequoia.Connective.Sum
import Sequoia.Connective.Tensor
import Sequoia.Connective.Top
import Sequoia.Connective.With
import Sequoia.Connective.Zero
import Sequoia.Context
import Sequoia.Disjunction
import Sequoia.Monad.Run
import Sequoia.Profunctor
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exp hiding (Coexp(..))

-- Expressions

data Expr ctx a b where
  Var :: IxL a ctx -> Expr ctx (E ctx) a
  RTop :: Expr ctx (E ctx) Top
  RWith :: Expr ctx (E ctx) a -> Expr ctx (E ctx) b -> Expr ctx (E ctx) (a & b)
  RSum1 :: Expr ctx (E ctx) a -> Expr ctx (E ctx) (a ⊕ b)
  RSum2 :: Expr ctx (E ctx) b -> Expr ctx (E ctx) (a ⊕ b)
  RBottom :: Expr ctx (E ctx) _Δ -> Expr ctx (E ctx) (Either _Δ (Bottom (R ctx)))
  ROne :: Expr ctx (E ctx) (One (E ctx))
  RPar :: Expr ctx (E ctx) (Either a b) -> Expr ctx (E ctx) (a ⅋ b)
  RTensor :: Expr ctx (E ctx) a -> Expr ctx (E ctx) b -> Expr ctx (E ctx) (a ⊗ b)
  RFun :: Expr (a < ctx) (E ctx) b -> Expr ctx (E ctx) (Fun (R ctx) a b)
  RSub :: Expr ctx (E ctx) a -> Expr ctx b (R ctx) -> Expr ctx (E ctx) (Sub (R ctx) b a)

  Covar :: IxR ctx b -> Expr ctx b (R ctx)
  LZero :: Expr ctx Zero (R ctx)
  LWith1 :: Expr ctx a (R ctx) -> Expr ctx (a & b) (R ctx)
  LWith2 :: Expr ctx b (R ctx) -> Expr ctx (a & b) (R ctx)
  LSum :: Expr ctx a (R ctx) -> Expr ctx b (R ctx) -> Expr ctx (a ⊕ b) (R ctx)
  LBottom :: Expr ctx (Bottom (R ctx)) (R ctx)
  LOne :: Expr ctx _Γ (R ctx) -> Expr ctx (One (E ctx), _Γ) (R ctx)
  LPar :: Expr ctx a (R ctx) -> Expr ctx b (R ctx) -> Expr ctx (a ⅋ b) (R ctx)
  LTensor :: Expr ctx (a, b) (R ctx) -> Expr ctx (a ⊗ b) (R ctx)
  LFun :: Expr ctx (E ctx) a -> Expr ctx b (R ctx) -> Expr ctx (Fun (R ctx) a b) (R ctx)
  LSub :: Expr (a < ctx) (E ctx) b -> Expr ctx (Sub (R ctx) b a) (R ctx)

deriving instance Show (Expr ctx a b)


-- Values

data Val ctx a b where
  VNe :: IxL a ctx -> Val ctx (E ctx) a
  VTop :: Val ctx (E ctx) Top
  VWith :: Val ctx (E ctx) a -> Val ctx (E ctx) b -> Val ctx (E ctx) (a & b)
  VSum1 :: Val ctx (E ctx) a -> Val ctx (E ctx) (a ⊕ b)
  VSum2 :: Val ctx (E ctx) b -> Val ctx (E ctx) (a ⊕ b)
  VOne :: Val ctx (E ctx) (One (E ctx))
  VPar :: Val ctx (E ctx) (Either a b) -> Val ctx (E ctx) (a ⅋ b)
  VTensor :: Val ctx (E ctx) a -> Val ctx (E ctx) b -> Val ctx (E ctx) (a ⊗ b)
  VFun :: (Val (a < ctx) (E ctx) a -> Val (a < ctx) (E ctx) b) -> Val ctx (E ctx) (Fun (R ctx) a b)
  VSub :: Val ctx (E ctx) a -> Val ctx b (R ctx) -> Val ctx (E ctx) (Sub (R ctx) b a)

  EZero :: Val ctx Zero (R ctx)
  EWith1 :: Val ctx a (R ctx) -> Val ctx (a & b) (R ctx)
  EWith2 :: Val ctx b (R ctx) -> Val ctx (a & b) (R ctx)
  ESum :: Val ctx a (R ctx) -> Val ctx b (R ctx) -> Val ctx (a ⊕ b) (R ctx)
  EBottom :: Val ctx (Bottom (R ctx)) (R ctx)
  EOne :: Val ctx a (R ctx) -> Val ctx (One (E ctx), a) (R ctx)
  EPar :: Val ctx a (R ctx) -> Val ctx b (R ctx) -> Val ctx (a ⅋ b) (R ctx)
  ETensor :: Val ctx (a, b) (R ctx) -> Val ctx (a ⊗ b) (R ctx)
  EFun :: Val ctx (E ctx) a -> Val ctx b (R ctx) -> Val ctx (Fun (R ctx) a b) (R ctx)
  ESub :: (Val (a < ctx) (E ctx) a -> Val (a < ctx) (E ctx) b) -> Val ctx (Sub (R ctx) b a) (R ctx)

bindVal :: (a -> b) -> (Val (x < ctx) (E ctx) x -> a) -> b
bindVal with b = with (b (VNe IxLZ))


-- Quotation

quoteVal :: Val ctx a b -> Expr ctx a b
quoteVal = \case
  VNe l       -> Var l
  VTop        -> RTop
  VWith a b   -> RWith (quoteVal a) (quoteVal b)
  VSum1 a     -> RSum1 (quoteVal a)
  VSum2 b     -> RSum2 (quoteVal b)
  VOne        -> ROne
  VPar a      -> RPar (quoteVal a)
  VTensor a b -> RTensor (quoteVal a) (quoteVal b)
  VFun f      -> RFun (quoteBinder f)
  VSub a b    -> RSub (quoteVal a) (quoteVal b)

  EZero       -> LZero
  EWith1 f    -> LWith1 (quoteVal f)
  EWith2 g    -> LWith2 (quoteVal g)
  ESum f g    -> LSum (quoteVal f) (quoteVal g)
  EBottom     -> LBottom
  EOne v      -> LOne (quoteVal v)
  EPar f g    -> LPar (quoteVal f) (quoteVal g)
  ETensor a   -> LTensor (quoteVal a)
  EFun a b    -> LFun (quoteVal a) (quoteVal b)
  ESub f      -> LSub (quoteBinder f)

quoteBinder :: (Val (t < ctx) (E ctx) t -> Val (t < ctx) (E ctx) u) -> Expr (t < ctx) (E ctx) u
quoteBinder = bindVal quoteVal


-- Evaluator

eval :: Eval e r a b -> (b • r) -> a • r
eval = getExp . getEval

coeval :: Eval e r a r -> (a • r)
coeval = (`eval` idK)

copure :: (a • r) -> Eval e r a r
copure = evaluator . (>>>)

evaluator :: ((b • r) -> (a • r)) -> Eval e r a b
evaluator = Eval . Exp

(<<>>) :: Disj d => Eval e r a s -> Eval e r b s -> Eval e r (a `d` b) s
f <<>> g = evaluator (\ k -> eval f k <••> eval g k)

infix 3 <<>>

newtype Eval e r a b = Eval { getEval :: Exp r a b }
  deriving (Applicative, Category, Functor, Monad, MonadRunK r, Profunctor)


evalFun :: Fun r a b -> Eval e r a b
evalFun = Eval . runFunExp


-- Definitional interpreter

evalDef :: Ctx ctx => ctx -> Expr ctx a b -> Eval (E ctx) (R ctx) a b
evalDef ctx = \case
  Var i       -> pure (i <! ctx)
  RTop        -> pure Top
  RWith a b   -> liftA2 inlr (evalDef ctx a) (evalDef ctx b)
  RSum1 a     -> inlF (evalDef ctx a)
  RSum2 b     -> inrF (evalDef ctx b)
  RBottom a   -> inlF (evalDef ctx a)
  ROne        -> pure (One (getE ctx))
  RPar a      -> coerceDisj <$> evalDef ctx a
  RTensor a b -> liftA2 inlr (evalDef ctx a) (evalDef ctx b)
  RFun f      -> pure (fun (\ b a -> eval (evalDef (a :< ctx) f) b • getE ctx))
  RSub a b    -> evalDef ctx a <&> (coeval (evalDef ctx b) :>-)

  Covar i     -> copure (ctx !> i)
  LZero       -> copure (K absurdP)
  LWith1 a    -> exlL (evalDef ctx a)
  LWith2 b    -> exrL (evalDef ctx b)
  LSum l r    -> evalDef ctx l <<>> evalDef ctx r
  LBottom     -> copure (K absurdN)
  LOne a      -> exrL (evalDef ctx a)
  LPar l r    -> evalDef ctx l <<>> evalDef ctx r
  LTensor a   -> evalDef ctx a <<^ coerceConj
  LFun a b    -> copure (K (\ f -> coeval (evalDef ctx a >>> evalFun f >>> evalDef ctx b) • getE ctx))
  LSub f      -> copure (K (\ (b :>- a) -> eval (evalDef (a :< ctx) f) b • getE ctx))


-- Execution

execVal :: Ctx ctx => ctx -> Val ctx a b -> Eval (E ctx) (R ctx) a b
execVal ctx = \case
  VNe i       -> pure (i <! ctx)
  VTop        -> pure Top
  VWith a b   -> liftA2 inlr (execVal ctx a) (execVal ctx b)
  VSum1 a     -> inlF (execVal ctx a)
  VSum2 b     -> inrF (execVal ctx b)
  VOne        -> pure (One (getE ctx))
  VPar a      -> coerceDisj <$> execVal ctx a
  VTensor a b -> liftA2 inlr (execVal ctx a) (execVal ctx b)
  VFun f      -> pure (fun (\ b a -> eval (bindVal (execVal (a :< ctx)) f) b • getE ctx))
  VSub a b    -> execVal ctx a <&> (coeval (execVal ctx b) :>-)

  EZero       -> copure (K absurdP)
  EWith1 a    -> exlL (execVal ctx a)
  EWith2 b    -> exrL (execVal ctx b)
  ESum a b    -> execVal ctx a <<>> execVal ctx b
  EBottom     -> copure (K absurdN)
  EOne a      -> exrL (execVal ctx a)
  EPar a b    -> execVal ctx a <<>> execVal ctx b
  ETensor a   -> execVal ctx a <<^ coerceConj
  EFun a b    -> copure (K (\ f -> coeval (execVal ctx a >>> evalFun f >>> execVal ctx b) • getE ctx))
  ESub f      -> copure (K (\ (b :>- a) -> eval (bindVal (execVal (a :< ctx)) f) b • getE ctx))
