{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Interpreter.Typed
( -- * Expressions
  Expr(..)
, Coexpr(..)
  -- * Values
, Val(..)
, Coval(..)
  -- * Quotation
, quoteVal
, quoteCoval
  -- * Definitional interpreter
, evalDef
, coevalDef
  -- * Execution
, execVal
, execCoval
) where

import Control.Applicative (liftA2)
import Data.Functor ((<&>))
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
import Sequoia.Profunctor
import Sequoia.Profunctor.Continuation

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
  RSub :: Expr ctx (E ctx) a -> Coexpr ctx b (R ctx) -> Expr ctx (E ctx) (Sub (R ctx) b a)

deriving instance Show (Expr ctx a b)

data Coexpr ctx a b where
  Covar :: IxR ctx b -> Coexpr ctx b (R ctx)
  LZero :: Coexpr ctx Zero (R ctx)
  LWith1 :: Coexpr ctx a (R ctx) -> Coexpr ctx (a & b) (R ctx)
  LWith2 :: Coexpr ctx b (R ctx) -> Coexpr ctx (a & b) (R ctx)
  LSum :: Coexpr ctx a (R ctx) -> Coexpr ctx b (R ctx) -> Coexpr ctx (a ⊕ b) (R ctx)
  LBottom :: Coexpr ctx (Bottom (R ctx)) (R ctx)
  LOne :: Coexpr ctx _Γ (R ctx) -> Coexpr ctx (One (E ctx), _Γ) (R ctx)
  LPar :: Coexpr ctx a (R ctx) -> Coexpr ctx b (R ctx) -> Coexpr ctx (a ⅋ b) (R ctx)
  LTensor :: Coexpr ctx (a, b) (R ctx) -> Coexpr ctx (a ⊗ b) (R ctx)
  LFun :: Expr ctx (E ctx) a -> Coexpr ctx b (R ctx) -> Coexpr ctx (Fun (R ctx) a b) (R ctx)
  LSub :: Expr (a < ctx) (E ctx) b -> Coexpr ctx (Sub (R ctx) b a) (R ctx)

deriving instance Show (Coexpr ctx a b)


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
  VSub :: Val ctx (E ctx) a -> Coval ctx b (R ctx) -> Val ctx (E ctx) (Sub (R ctx) b a)

data Coval ctx a b where
  EZero :: Coval ctx Zero (R ctx)
  EWith1 :: Coval ctx a (R ctx) -> Coval ctx (a & b) (R ctx)
  EWith2 :: Coval ctx b (R ctx) -> Coval ctx (a & b) (R ctx)
  ESum :: Coval ctx a (R ctx) -> Coval ctx b (R ctx) -> Coval ctx (a ⊕ b) (R ctx)
  EBottom :: Coval ctx (Bottom (R ctx)) (R ctx)
  EOne :: Coval ctx a (R ctx) -> Coval ctx (One (E ctx), a) (R ctx)
  EPar :: Coval ctx a (R ctx) -> Coval ctx b (R ctx) -> Coval ctx (a ⅋ b) (R ctx)
  ETensor :: Coval ctx (a, b) (R ctx) -> Coval ctx (a ⊗ b) (R ctx)
  EFun :: Val ctx (E ctx) a -> Coval ctx b (R ctx) -> Coval ctx (Fun (R ctx) a b) (R ctx)
  ESub :: (Val (a < ctx) (E ctx) a -> Val (a < ctx) (E ctx) b) -> Coval ctx (Sub (R ctx) b a) (R ctx)

bindVal :: (a -> b) -> (Val (x < ctx) (E ctx) x -> a) -> b
bindVal with b = with (b (VNe IxLZ))


-- Quotation

quoteVal :: Val ctx (E ctx) b -> Expr ctx (E ctx) b
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
  VSub a b    -> RSub (quoteVal a) (quoteCoval b)

quoteCoval :: Coval ctx a (R ctx) -> Coexpr ctx a (R ctx)
quoteCoval = \case
  EZero     -> LZero
  EWith1 f  -> LWith1 (quoteCoval f)
  EWith2 g  -> LWith2 (quoteCoval g)
  ESum f g  -> LSum (quoteCoval f) (quoteCoval g)
  EBottom   -> LBottom
  EOne v    -> LOne (quoteCoval v)
  EPar f g  -> LPar (quoteCoval f) (quoteCoval g)
  ETensor a -> LTensor (quoteCoval a)
  EFun a b  -> LFun (quoteVal a) (quoteCoval b)
  ESub f    -> LSub (quoteBinder f)

quoteBinder :: (Val (t < ctx) (E ctx) t -> Val (t < ctx) (E ctx) u) -> Expr (t < ctx) (E ctx) u
quoteBinder = bindVal quoteVal


-- Definitional interpreter

evalDef :: Ctx ctx => ctx -> Expr ctx (E ctx) b -> DN (R ctx) b
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
  RFun f      -> pure (fun (\ b a -> runDN (evalDef (a :< ctx) f) • b))
  RSub a b    -> evalDef ctx a <&> (coevalDef ctx b :>-)

coevalDef :: Ctx ctx => ctx -> Coexpr ctx a (R ctx) -> (a • R ctx)
coevalDef ctx = \case
  Covar i   -> ctx !> i
  LZero     -> K absurdP
  LWith1 a  -> exlL (coevalDef ctx a)
  LWith2 b  -> exrL (coevalDef ctx b)
  LSum l r  -> coevalDef ctx l <••> coevalDef ctx r
  LBottom   -> K absurdN
  LOne a    -> exrL (coevalDef ctx a)
  LPar l r  -> coevalDef ctx l <••> coevalDef ctx r
  LTensor a -> coevalDef ctx a <<^ coerceConj
  LFun a b  -> K (\ f -> runDN (evalDef ctx a >>= appFun f) • coevalDef ctx b)
  LSub f    -> K (\ (b :>- a) -> runDN (evalDef (a :< ctx) f) • b)


-- Execution

execVal :: Ctx ctx => ctx -> Val ctx (E ctx) a -> DN (R ctx) a
execVal ctx = \case
  VNe i       -> pure (i <! ctx)
  VTop        -> pure Top
  VWith a b   -> liftA2 inlr (execVal ctx a) (execVal ctx b)
  VSum1 a     -> inlF (execVal ctx a)
  VSum2 b     -> inrF (execVal ctx b)
  VOne        -> pure (One (getE ctx))
  VPar a      -> coerceDisj <$> execVal ctx a
  VTensor a b -> liftA2 inlr (execVal ctx a) (execVal ctx b)
  VFun f      -> pure (fun (\ b a -> runDN (bindVal (execVal (a :< ctx)) f) • b))
  VSub a b    -> execVal ctx a <&> (execCoval ctx b :>-)

execCoval :: Ctx ctx => ctx -> Coval ctx a (R ctx) -> (a • R ctx)
execCoval ctx = \case
  EZero     -> K absurdP
  EWith1 a  -> exlL (execCoval ctx a)
  EWith2 b  -> exrL (execCoval ctx b)
  ESum a b  -> execCoval ctx a <••> execCoval ctx b
  EBottom   -> K absurdN
  EOne a    -> exrL (execCoval ctx a)
  EPar a b  -> execCoval ctx a <••> execCoval ctx b
  ETensor a -> execCoval ctx a <<^ coerceConj
  EFun a b  -> K (\ f -> runDN (execVal ctx a >>= appFun f) • execCoval ctx b)
  ESub f    -> K (\ (b :>- a) -> runDN (bindVal (execVal (a :< ctx)) f) • b)
