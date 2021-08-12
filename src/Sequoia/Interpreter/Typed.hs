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
  -- * Sequents
, type (|-)(..)
, (<|)
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
  Var :: IxL a as -> Expr (as |- bs) (E as) a
  RTop :: Expr (as |- bs) (E as) Top
  RWith :: Expr (as |- bs) (E as) a -> Expr (as |- bs) (E as) b -> Expr (as |- bs) (E as) (a & b)
  RSum1 :: Expr (as |- bs) (E as) a -> Expr (as |- bs) (E as) (a ⊕ b)
  RSum2 :: Expr (as |- bs) (E as) b -> Expr (as |- bs) (E as) (a ⊕ b)
  RBottom :: Expr (as |- bs) (E as) _Δ -> Expr (as |- bs) (E as) (Either _Δ (Bottom (R bs)))
  ROne :: Expr (as |- bs) (E as) (One (E as))
  RPar :: Expr (as |- bs) (E as) (Either a b) -> Expr (as |- bs) (E as) (a ⅋ b)
  RTensor :: Expr (as |- bs) (E as) a -> Expr (as |- bs) (E as) b -> Expr (as |- bs) (E as) (a ⊗ b)
  RFun :: Expr ((a < as) |- bs) (E as) b -> Expr (as |- bs) (E as) (Fun (R bs) a b)
  RSub :: Expr (as |- bs) (E as) a -> Coexpr (as |- bs) b (R bs) -> Expr (as |- bs) (E as) (Sub (R bs) b a)

deriving instance Show (Expr ctx a b)

data Coexpr ctx a b where
  Covar :: IxR bs b -> Coexpr (as |- bs) b (R bs)
  LZero :: Coexpr (as |- bs) Zero (R bs)
  LWith1 :: Coexpr (as |- bs) a (R bs) -> Coexpr (as |- bs) (a & b) (R bs)
  LWith2 :: Coexpr (as |- bs) b (R bs) -> Coexpr (as |- bs) (a & b) (R bs)
  LSum :: Coexpr (as |- bs) a (R bs) -> Coexpr (as |- bs) b (R bs) -> Coexpr (as |- bs) (a ⊕ b) (R bs)
  LBottom :: Coexpr (as |- bs) (Bottom (R bs)) (R bs)
  LOne :: Coexpr (as |- bs) _Γ (R bs) -> Coexpr (as |- bs) (One (E as), _Γ) (R bs)
  LPar :: Coexpr (as |- bs) a (R bs) -> Coexpr (as |- bs) b (R bs) -> Coexpr (as |- bs) (a ⅋ b) (R bs)
  LTensor :: Coexpr (as |- bs) (a, b) (R bs) -> Coexpr (as |- bs) (a ⊗ b) (R bs)
  LFun :: Expr (as |- bs) (E as) a -> Coexpr (as |- bs) b (R bs) -> Coexpr (as |- bs) (Fun (R bs) a b) (R bs)
  LSub :: Expr ((a < as) |- bs) (E as) b -> Coexpr (as |- bs) (Sub (R bs) b a) (R bs)

deriving instance Show (Coexpr ctx a b)


-- Values

data Val ctx a where
  VNe :: IxL a as -> Val (as |- bs) a
  VTop :: Val ctx Top
  VWith :: Val ctx a -> Val ctx b -> Val ctx (a & b)
  VSum1 :: Val ctx a -> Val ctx (a ⊕ b)
  VSum2 :: Val ctx b -> Val ctx (a ⊕ b)
  VOne :: Val (as |- bs) (One (E as))
  VPar :: Val ctx (Either a b) -> Val ctx (a ⅋ b)
  VTensor :: Val ctx a -> Val ctx b -> Val ctx (a ⊗ b)
  VFun :: (Val (a < as |- bs) a -> Val ((a < as) |- bs) b) -> Val (as |- bs) (Fun (R bs) a b)
  VSub :: Val (as |- bs) a -> Coval (as |- bs) b -> Val (as |- bs) (Sub (R bs) b a)

data Coval ctx a where
  EZero :: Coval ctx Zero
  EWith1 :: Coval ctx a -> Coval ctx (a & b)
  EWith2 :: Coval ctx b -> Coval ctx (a & b)
  ESum :: Coval ctx a -> Coval ctx b -> Coval ctx (a ⊕ b)
  EBottom :: Coval (as |- bs) (Bottom (R bs))
  EOne :: Coval (as |- bs) a -> Coval (as |- bs) (One (E as), a)
  EPar :: Coval ctx a -> Coval ctx b -> Coval ctx (a ⅋ b)
  ETensor :: Coval ctx (a, b) -> Coval ctx (a ⊗ b)
  EFun :: Val (as |- bs) a -> Coval (as |- bs) b -> Coval (as |- bs) (Fun (R bs) a b)
  ESub :: (Val (a < as |- bs) a -> Val ((a < as) |- bs) b) -> Coval (as |- bs) (Sub (R bs) b a)

bindVal :: (a -> b) -> (Val (x < as |- bs) x -> a) -> b
bindVal with b = with (b (VNe IxLZ))


-- Quotation

quoteVal :: Val (as |- bs) b -> Expr (as |- bs) (E as) b
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

quoteCoval :: Coval (as |- bs) a -> Coexpr (as |- bs) a (R bs)
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

quoteBinder :: (Val (t < as |- bs) t -> Val ((t < as) |- bs) u) -> Expr ((t < as) |- bs) (E as) u
quoteBinder = bindVal quoteVal


-- Definitional interpreter

evalDef :: (LCtx as, RCtx bs) => as |- bs -> Expr (as |- bs) (E as) b -> DN (R bs) b
evalDef ctx@(_Γ :|-: _Δ) = \case
  Var i       -> pure (i <! _Γ)
  RTop        -> pure Top
  RWith a b   -> liftA2 inlr (evalDef ctx a) (evalDef ctx b)
  RSum1 a     -> inlF (evalDef ctx a)
  RSum2 b     -> inrF (evalDef ctx b)
  RBottom a   -> inlF (evalDef ctx a)
  ROne        -> pure (One (getE _Γ))
  RPar a      -> coerceDisj <$> evalDef ctx a
  RTensor a b -> liftA2 inlr (evalDef ctx a) (evalDef ctx b)
  RFun f      -> pure (fun (\ b a -> runDN (evalDef (a <| ctx) f) • b))
  RSub a b    -> evalDef ctx a <&> (coevalDef ctx b :>-)

coevalDef :: (LCtx as, RCtx bs) => as |- bs -> Coexpr (as |- bs) a (R bs) -> (a • R bs)
coevalDef ctx@(_Γ :|-: _Δ) = \case
  Covar i   -> _Δ !> i
  LZero     -> K absurdP
  LWith1 a  -> exlL (coevalDef ctx a)
  LWith2 b  -> exrL (coevalDef ctx b)
  LSum l r  -> coevalDef ctx l <••> coevalDef ctx r
  LBottom   -> K absurdN
  LOne a    -> exrL (coevalDef ctx a)
  LPar l r  -> coevalDef ctx l <••> coevalDef ctx r
  LTensor a -> coevalDef ctx a <<^ coerceConj
  LFun a b  -> K (\ f -> runDN (evalDef ctx a >>= appFun f) • coevalDef ctx b)
  LSub f    -> K (\ (b :>- a) -> runDN (evalDef (a <| ctx) f) • b)


-- Execution

execVal :: (LCtx as, RCtx bs) => as |- bs -> Val (as |- bs) a -> DN (R bs) a
execVal ctx@(_Γ :|-: _Δ) = \case
  VNe i       -> pure (i <! _Γ)
  VTop        -> pure Top
  VWith a b   -> liftA2 inlr (execVal ctx a) (execVal ctx b)
  VSum1 a     -> inlF (execVal ctx a)
  VSum2 b     -> inrF (execVal ctx b)
  VOne        -> pure (One (getE _Γ))
  VPar a      -> coerceDisj <$> execVal ctx a
  VTensor a b -> liftA2 inlr (execVal ctx a) (execVal ctx b)
  VFun f      -> pure (fun (\ b a -> runDN (bindVal (execVal (a <| ctx)) f) • b))
  VSub a b    -> execVal ctx a <&> (execCoval ctx b :>-)

execCoval :: (LCtx as, RCtx bs) => as |- bs -> Coval (as |- bs) a -> (a • R bs)
execCoval ctx@(_Γ :|-: _Δ) = \case
  EZero     -> K absurdP
  EWith1 a  -> exlL (execCoval ctx a)
  EWith2 b  -> exrL (execCoval ctx b)
  ESum a b  -> execCoval ctx a <••> execCoval ctx b
  EBottom   -> K absurdN
  EOne a    -> exrL (execCoval ctx a)
  EPar a b  -> execCoval ctx a <••> execCoval ctx b
  ETensor a -> execCoval ctx a <<^ coerceConj
  EFun a b  -> K (\ f -> runDN (execVal ctx a >>= appFun f) • execCoval ctx b)
  ESub f    -> K (\ (b :>- a) -> runDN (bindVal (execVal (a <| ctx)) f) • b)


-- Sequents

data as |- bs = as :|-: bs

infix 3 |-, :|-:

(|-) :: as -> bs -> as |- bs
(|-) = (:|-:)

(<|) :: a -> as |- bs -> a < as |- bs
a <| (as :|-: bs) = a :< as |- bs

infixr 4 <|
