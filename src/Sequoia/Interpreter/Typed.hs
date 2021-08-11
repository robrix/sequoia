{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Interpreter.Typed
( -- * Terms
  Term(..)
, Coterm(..)
, FO(..)
, HO(..)
, ShowTerm(..)
, ShowBinder(..)
  -- * Expressions
, Expr(..)
, Coexpr(..)
, Scope(..)
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

import Data.Functor.Classes
import Sequoia.Conjunction
import Sequoia.Connective.Bottom
import Sequoia.Connective.Not
import Sequoia.Connective.One
import Sequoia.Connective.Sum
import Sequoia.Connective.Tensor
import Sequoia.Connective.Top
import Sequoia.Connective.With
import Sequoia.Connective.Zero
import Sequoia.Context
import Sequoia.Disjunction

-- Terms

data Term binder ctx a where
  TVar :: IxL a _Γ -> Term binder ctx a
  TTop :: Term binder ctx Top
  TWith :: Term binder ctx a -> Term binder ctx b -> Term binder ctx (a & b)
  TSum1 :: Term binder ctx a -> Term binder ctx (a ⊕ b)
  TSum2 :: Term binder ctx b -> Term binder ctx (a ⊕ b)
  TBot :: Term binder (as |- bs) _Δ -> Term binder (as |- bs) (_Δ `Either` Bottom (R bs))
  TOne :: Term binder (as |- bs) (One (E as))
  TTensor :: Term binder ctx a -> Term binder ctx b -> Term binder ctx (a ⊗ b)
  TFun :: binder _Γ _Δ a b -> Term binder (_Γ |- _Δ) (a -> b)
  TNot :: Coterm binder ctx a -> Term binder ctx (Not a r)

instance ShowBinder binder => Show (Term binder (_Γ |- _Δ) a) where
  showsPrec = showsTerm

data Coterm binder ctx a where
  CVar :: IxR _Δ a -> Coterm binder ctx a
  CZero :: Coterm binder ctx Zero
  CWith1 :: Coterm binder ctx a -> Coterm binder ctx (a & b)
  CWith2 :: Coterm binder ctx b -> Coterm binder ctx (a & b)
  CSum :: Coterm binder ctx a -> Coterm binder ctx b -> Coterm binder ctx (a ⊕ b)
  CBot :: Coterm binder (as |- bs) (Bottom (R bs))
  COne :: Coterm binder (as |- bs) _Γ -> Coterm binder (as |- bs) (One (E as), _Γ)
  CFun :: Term binder ctx a -> Coterm binder ctx b -> Coterm binder ctx (a -> b)
  CNot :: Term binder ctx a -> Coterm binder ctx (Not a r)

deriving instance ShowBinder binder => Show (Coterm binder (_Γ |- _Δ) a)


newtype FO _Γ _Δ a b = FO (Term FO ((a < _Γ) |- _Δ) b)

newtype HO _Γ _Δ a b = HO (Term HO (_Γ |- _Δ) a -> Term HO ((a < _Γ) |- _Δ) b)


class ShowTerm t where
  showsTerm :: Int -> t a -> ShowS

instance ShowBinder binder => ShowTerm (Term binder (_Γ |- _Δ)) where
  showsTerm p = \case
    TVar i      -> showsUnaryWith showsPrec "TVar" p i
    TTop        -> showString "TTop"
    TWith a b   -> showsBinaryWith showsTerm showsTerm "TWith" p a b
    TSum1 a     -> showsUnaryWith showsTerm "TSum1" p a
    TSum2 b     -> showsUnaryWith showsTerm "TSum2" p b
    TBot a      -> showsUnaryWith showsTerm "TBot" p a
    TOne        -> showString "TOne"
    TTensor a b -> showsBinaryWith showsTerm showsTerm "TWith" p a b
    TFun f      -> showsUnaryWith showsBinder "TFun" p f
    TNot k      -> showsUnaryWith showsTerm "TNot" p k

instance ShowBinder binder => ShowTerm (Coterm binder (_Γ |- _Δ)) where
  showsTerm p = \case
    CVar i   -> showsUnaryWith showsPrec "CVar" p i
    CZero    -> showString "CZero"
    CWith1 f -> showsUnaryWith showsTerm "CWith1" p f
    CWith2 g -> showsUnaryWith showsTerm "CWith2" p g
    CSum f g -> showsBinaryWith showsTerm showsTerm "CSum" p f g
    CBot     -> showString "CBot"
    COne a   -> showsUnaryWith showsTerm "COne" p a
    CFun a b -> showsBinaryWith showsTerm showsTerm "CFun" p a b
    CNot a   -> showsUnaryWith showsTerm "CNot" p a

class ShowBinder t where
  showsBinder :: Int -> t _Γ _Δ a b -> ShowS

instance ShowBinder FO where
  showsBinder p (FO t) = showsUnaryWith showsTerm "FO" p t

instance ShowBinder HO where
  showsBinder p (HO t) = showsUnaryWith (\ p f -> showsTerm p (f (TVar IxLZ))) "HO" p t


-- Expressions

data Expr ctx a where
  Var :: IxL a as -> Expr (as |- bs) a
  RTop :: Expr ctx Top
  RWith :: Expr ctx a -> Expr ctx b -> Expr ctx (a & b)
  RSum1 :: Expr ctx a -> Expr ctx (a ⊕ b)
  RSum2 :: Expr ctx b -> Expr ctx (a ⊕ b)
  RBot :: Expr (as |- bs) _Δ -> Expr (as |- bs) (Either _Δ (Bottom (R bs)))
  ROne :: Expr (as |- bs) (One (E as))
  RTensor :: Expr ctx a -> Expr ctx b -> Expr ctx (a ⊗ b)
  RFun :: Scope as bs a b -> Expr (as |- bs) (a -> b)

deriving instance Show (Expr ctx a)

data Coexpr ctx a where
  Covar :: IxR bs b -> Coexpr (as |- bs) b
  LZero :: Coexpr ctx Zero
  LWith1 :: Coexpr ctx a -> Coexpr ctx (a & b)
  LWith2 :: Coexpr ctx b -> Coexpr ctx (a & b)
  LSum :: Coexpr ctx a -> Coexpr ctx b -> Coexpr ctx (a ⊕ b)
  LBot :: Coexpr (as |- bs) (Bottom (R bs))
  LOne :: Coexpr (as |- bs) _Γ -> Coexpr (as |- bs) (One (E as), _Γ)
  LFun :: Expr ctx a -> Coexpr ctx b -> Coexpr ctx (a -> b)

deriving instance Show (Coexpr ctx a)

newtype Scope as bs a b = Scope { getScope :: Expr ((a < as) |- bs) b }
  deriving (Show)


-- Values

data Val ctx a where
  VNe :: IxL a as -> Val (as |- bs) a
  VTop :: Val ctx Top
  VWith :: Val ctx a -> Val ctx b -> Val ctx (a & b)
  VSum1 :: Val ctx a -> Val ctx (a ⊕ b)
  VSum2 :: Val ctx b -> Val ctx (a ⊕ b)
  VOne :: Val (as |- bs) (One (E as))
  VFun :: (Val (a < as |- bs) a -> Val ((a < as) |- bs) b) -> Val (as |- bs) (a -> b)

data Coval ctx a where
  EZero :: Coval ctx Zero
  EWith1 :: Coval ctx a -> Coval ctx (a & b)
  EWith2 :: Coval ctx b -> Coval ctx (a & b)
  ESum :: Coval ctx a -> Coval ctx b -> Coval ctx (a ⊕ b)
  EBottom :: Coval (as |- bs) (Bottom (R bs))
  EOne :: Coval (as |- bs) a -> Coval (as |- bs) (One (E as), a)
  EFun :: Val ctx a -> Coval ctx b -> Coval ctx (a -> b)

bindVal :: (a -> b) -> (Val (x < as |- bs) x -> a) -> b
bindVal with b = with (b (VNe IxLZ))


-- Quotation

quoteVal :: Val (as |- bs) a -> Expr (as |- bs) a
quoteVal = \case
  VNe l     -> Var l
  VTop      -> RTop
  VWith a b -> RWith (quoteVal a) (quoteVal b)
  VSum1 a   -> RSum1 (quoteVal a)
  VSum2 b   -> RSum2 (quoteVal b)
  VOne      -> ROne
  VFun f    -> RFun (quoteBinder f)

quoteCoval :: Coval (as |- bs) a -> Coexpr (as |- bs) a
quoteCoval = \case
  EZero    -> LZero
  EWith1 f -> LWith1 (quoteCoval f)
  EWith2 g -> LWith2 (quoteCoval g)
  ESum f g -> LSum (quoteCoval f) (quoteCoval g)
  EBottom  -> LBot
  EOne v   -> LOne (quoteCoval v)
  EFun a b -> LFun (quoteVal a) (quoteCoval b)

quoteBinder :: (Val (t < as |- bs) t -> Val ((t < as) |- bs) u) -> Scope as bs t u
quoteBinder = Scope . bindVal quoteVal


-- Definitional interpreter

evalDef :: LCtx as => as |- bs -> Expr (as |- bs) a -> a
evalDef ctx@(_Γ :|-: _Δ) = \case
  Var i       -> i <! _Γ
  RTop        -> Top
  RWith a b   -> evalDef ctx a >--< evalDef ctx b
  RSum1 a     -> InL (evalDef ctx a)
  RSum2 b     -> InR (evalDef ctx b)
  RBot a      -> Left (evalDef ctx a)
  ROne        -> One (getE _Γ)
  RTensor a b -> evalDef ctx a >--< evalDef ctx b
  RFun b      -> \ a -> evalDef (a <| ctx) (getScope b)

coevalDef :: (LCtx as, RCtx bs) => as |- bs -> Coexpr (as |- bs) a -> (a -> R bs)
coevalDef ctx@(_Γ :|-: _Δ) = \case
  Covar i  -> _Δ !> i
  LZero    -> absurdP
  LWith1 a -> coevalDef ctx a . exl
  LWith2 b -> coevalDef ctx b . exr
  LSum l r -> coevalDef ctx l <--> coevalDef ctx r
  LBot     -> absurdN
  LOne a   -> coevalDef ctx a . snd
  LFun a b -> \ f -> coevalDef ctx b (f (evalDef ctx a))


-- Execution

execVal :: LCtx as => as |- bs -> Val (as |- bs) a -> a
execVal ctx@(_Γ :|-: _Δ) = \case
  VNe i     -> i <! _Γ
  VTop      -> Top
  VWith a b -> execVal ctx a >--< execVal ctx b
  VSum1 a   -> InL (execVal ctx a)
  VSum2 b   -> InR (execVal ctx b)
  VOne      -> One (getE _Γ)
  VFun f    -> \ a -> bindVal (execVal (a <| ctx)) f

execCoval :: (LCtx as, RCtx bs) => as |- bs -> Coval (as |- bs) a -> (a -> R bs)
execCoval ctx@(_Γ :|-: _Δ) = \case
  EZero    -> absurdP
  EWith1 a -> execCoval ctx a . exl
  EWith2 b -> execCoval ctx b . exr
  ESum a b -> execCoval ctx a <--> execCoval ctx b
  EBottom  -> absurdN
  EOne a   -> execCoval ctx a . snd
  EFun a b -> \ f -> execCoval ctx b (f (execVal ctx a))


-- Sequents

data as |- bs = as :|-: bs

infix 3 |-, :|-:

(|-) :: as -> bs -> as |- bs
(|-) = (:|-:)

(<|) :: a -> as |- bs -> a < as |- bs
a <| (as :|-: bs) = a :< as |- bs

infixr 4 <|
