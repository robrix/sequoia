{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Sequoia.Interpreter.Typed
( -- * Terms
  Term(..)
, Coterm(..)
, FO(..)
  -- * Expressions
, Expr(..)
, Coexpr(..)
, Scope(..)
  -- * Values
, Val(..)
, Coval(..)
  -- * Definitional interpreter
, evalDef
, coevalDef
  -- * Environments
, Γ(..)
, (<!)
, Δ(..)
, (!>)
, type (|-)(..)
, IxL(..)
, IxR(..)
) where

import Data.Functor.Classes
import Data.Void
import Sequoia.Conjunction
import Sequoia.Connective.Bottom
import Sequoia.Connective.Not
import Sequoia.Connective.One
import Sequoia.Connective.Sum
import Sequoia.Connective.Top
import Sequoia.Connective.With
import Sequoia.Connective.Zero
import Sequoia.DeBruijn
import Sequoia.Disjunction

-- Terms

data Term binder e r _Γ _Δ a where
  TVar :: IxL a _Γ -> Term binder e r _Γ _Δ a
  TTop :: Term binder e r _Γ _Δ Top
  TWith :: Term binder e r _Γ _Δ a -> Term binder e r _Γ _Δ b -> Term binder e r _Γ _Δ (a & b)
  TSum1 :: Term binder e r _Γ _Δ a -> Term binder e r _Γ _Δ (a ⊕ b)
  TSum2 :: Term binder e r _Γ _Δ b -> Term binder e r _Γ _Δ (a ⊕ b)
  TBot :: Term binder e r _Γ _Δ _Δ -> Term binder e r _Γ _Δ (_Δ `Either` Bottom Void)
  TOne :: Term binder e r _Γ _Δ (One ())
  TFun :: binder e r _Γ _Δ a b -> Term binder e r _Γ _Δ (a -> b)
  TNot :: Coterm binder e r _Γ _Δ a -> Term binder e r _Γ _Δ (Not a r)

instance Show2 (binder e r _Γ _Δ) => Show (Term binder e r _Γ _Δ a) where
  showsPrec p = \case
    TVar i    -> showsUnaryWith showsPrec "TVar" p i
    TTop      -> showString "TTop"
    TWith a b -> showsBinaryWith showsPrec showsPrec "TWith" p a b
    TSum1 a   -> showsUnaryWith showsPrec "TSum1" p a
    TSum2 b   -> showsUnaryWith showsPrec "TSum2" p b
    TBot a    -> showsUnaryWith showsPrec "TBot" p a
    TOne      -> showString "TOne"
    TFun f    -> liftShowsPrec2 (const (const id)) (const id) (const (const id)) (const id) p f
    TNot k    -> showsUnaryWith showsPrec "TNot" p k

data Coterm binder e r _Γ _Δ a where
  CVar :: IxR _Δ a -> Coterm binder e r _Γ _Δ a
  CZero :: Coterm binder e r _Γ _Δ Zero
  CWith1 :: Coterm binder e r _Γ _Δ a -> Coterm binder e r _Γ _Δ (a & b)
  CWith2 :: Coterm binder e r _Γ _Δ b -> Coterm binder e r _Γ _Δ (a & b)
  CSum :: Coterm binder e r _Γ _Δ a -> Coterm binder e r _Γ _Δ b -> Coterm binder e r _Γ _Δ (a ⊕ b)
  CBot :: Coterm binder e r _Γ _Δ (Bottom Void)
  COne :: Coterm binder e r _Γ _Δ _Γ -> Coterm binder e r _Γ _Δ (One (), _Γ)
  CFun :: Term binder e r _Γ _Δ a -> Coterm binder e r _Γ _Δ b -> Coterm binder e r _Γ _Δ (a -> b)
  CNot :: Term binder e r _Γ _Δ a -> Coterm binder e r _Γ _Δ (Not a r)

deriving instance Show2 (binder e r _Γ _Δ) => Show (Coterm binder e r _Γ _Δ a)


newtype FO e r _Γ _Δ a b = FO (Term FO e r (a, _Γ) _Δ b)

instance Show2 (FO e r _Γ _Δ) where
  liftShowsPrec2 _ _ _ _ p (FO t) = showsUnaryWith showsPrec "FO" p t


class ShowTerm t where
  showsTerm :: Level -> Int -> t a -> ShowS

instance ShowBinder binder => ShowTerm (Term binder e r _Γ _Δ) where
  showsTerm d p = \case
    TVar i    -> showsUnaryWith showsPrec "TVar" p i
    TTop      -> showString "TTop"
    TWith a b -> showsBinaryWith (showsTerm d) (showsTerm d) "TWith" p a b
    TSum1 a   -> showsUnaryWith (showsTerm d) "TSum1" p a
    TSum2 b   -> showsUnaryWith (showsTerm d) "TSum2" p b
    TBot a    -> showsUnaryWith (showsTerm d) "TBot" p a
    TOne      -> showString "TOne"
    TFun f    -> showsUnaryWith (showsBinder d) "TFun" p f
    TNot k    -> showsUnaryWith (showsTerm d) "TNot" p k

instance ShowBinder binder => ShowTerm (Coterm binder e r _Γ _Δ) where
  showsTerm d p = \case
    CVar i   -> showsUnaryWith showsPrec "CVar" p i
    CZero    -> showString "CZero"
    CWith1 f -> showsUnaryWith (showsTerm d) "CWith1" p f
    CWith2 g -> showsUnaryWith (showsTerm d) "CWith2" p g
    CSum f g -> showsBinaryWith (showsTerm d) (showsTerm d) "CSum" p f g
    CBot     -> showString "CBot"
    COne a   -> showsUnaryWith (showsTerm d) "COne" p a
    CFun a b -> showsBinaryWith (showsTerm d) (showsTerm d) "CFun" p a b
    CNot a   -> showsUnaryWith (showsTerm d) "CNot" p a

class ShowBinder t where
  showsBinder :: Level -> Int -> t e r _Γ _Δ a b -> ShowS

instance ShowBinder FO where
  showsBinder d p (FO t) = showsUnaryWith (showsTerm (succ d)) "FO" p t


-- Expressions

data Expr as bs a where
  Var :: IxL a as -> Expr as bs a
  RTop :: Expr as bs Top
  RWith :: Expr as bs a -> Expr as bs b -> Expr as bs (a & b)
  RSum1 :: Expr as bs a -> Expr as bs (a ⊕ b)
  RSum2 :: Expr as bs b -> Expr as bs (a ⊕ b)
  RBot :: Expr as bs _Δ -> Expr as bs (Either _Δ (Bottom Void))
  ROne :: Expr as bs (One ())
  RFun :: Scope as bs a b -> Expr as bs (a -> b)

deriving instance Show (Expr as bs a)

data Coexpr as bs a where
  Covar :: IxR bs a -> Coexpr as bs a
  LZero :: Coexpr as bs Zero
  LWith1 :: Coexpr as bs a -> Coexpr as bs (a & b)
  LWith2 :: Coexpr as bs b -> Coexpr as bs (a & b)
  LSum :: Coexpr as bs a -> Coexpr as bs b -> Coexpr as bs (a ⊕ b)
  LBot :: Coexpr as bs (Bottom Void)
  LOne :: Coexpr as bs _Γ -> Coexpr as bs (One (), _Γ)
  LFun :: Expr as bs a -> Coexpr as bs b -> Coexpr as bs (a -> b)

deriving instance Show (Coexpr as bs a)

newtype Scope as bs a b = Scope { getScope :: Expr (a, as) bs b }
  deriving (Show)


-- Values

data Val as bs a where
  VTop :: Val as bs Top
  VWith :: Val as bs a -> Val as bs b -> Val as bs (a & b)
  VSum1 :: Val as bs a -> Val as bs (a ⊕ b)
  VSum2 :: Val as bs b -> Val as bs (a ⊕ b)
  VBottom :: Val as bs (Bottom Void)
  VOne :: Val as bs (One ())
  VFun :: (Val as bs a -> Val as bs b) -> Val as bs (a -> b)

data Coval as bs a where
  EZero :: Coval as bs Zero
  EWith1 :: Coval as bs a -> Coval as bs (a & b)
  EWith2 :: Coval as bs b -> Coval as bs (a & b)
  ESum :: Coval as bs a -> Coval as bs b -> Coval as bs (a ⊕ b)
  EBottom :: Coval as bs (Bottom Void)
  EOne :: Coval as bs a -> Coval as bs (One (), a)
  EFun :: Val as bs a -> Coval as bs b -> Coval as bs (a -> b)


-- Definitional interpreter

evalDef :: (as |- bs) e r -> Expr as bs a -> a
evalDef ctx = \case
  Var i     -> i <! ctx
  RTop      -> Top
  RWith a b -> evalDef ctx a >--< evalDef ctx b
  RSum1 a   -> InL (evalDef ctx a)
  RSum2 b   -> InR (evalDef ctx b)
  RBot a    -> Left (evalDef ctx a)
  ROne      -> One ()
  RFun b    -> \ a -> evalDef (a :<< ctx) (getScope b)

coevalDef :: (as |- bs) e r -> Coexpr as bs a -> (a -> r)
coevalDef ctx = \case
  Covar i  -> ctx !> i
  LZero    -> absurdP
  LWith1 a -> coevalDef ctx a . exl
  LWith2 b -> coevalDef ctx b . exr
  LSum l r -> coevalDef ctx l <--> coevalDef ctx r
  LBot     -> absurd . absurdN
  LOne a   -> coevalDef ctx a . snd
  LFun a b -> \ f -> coevalDef ctx b (f (evalDef ctx a))


-- Environments

data Γ e as where
  Γ :: Γ e (One e)
  (:<) :: a -> Γ e b -> Γ e (a, b)

infixr 5 :<

(<!) :: IxL a as -> (as |- bs) e r -> a
i      <! (c :>> _) = i <! c
IxLZ   <! (h :<< _) = h
IxLS i <! (_ :<< c) = i <! c

infixr 2 <!


data Δ r as where
  Δ :: r -> Δ r (Bottom r)
  (:>) :: Δ r a -> (b -> r) -> Δ r (a, b)

infixl 5 :>

(!>) :: (as |- bs) e r -> IxR bs b -> (b -> r)
delta !> ix = case (ix, delta) of
  (i,      _ :<< c) -> c !> i
  (IxRZ,   _ :>> r) -> r
  (IxRS i, c :>> _) -> c !> i

infixl 2 !>


data (a |- b) e r where
  ΓΔ :: (One e |- Bottom r) e r
  (:<<) :: a -> (as |- bs) e r -> ((a, as) |- bs) e r
  (:>>) :: (as |- bs) e r -> (b -> r) -> (as |- (bs, b)) e r

infix 3 |-
infixr 5 :<<
infixl 5 :>>


data IxL a as where
  IxLZ :: IxL a (a, b)
  IxLS :: IxL c b -> IxL c (a, b)

deriving instance Show (IxL as a)

data IxR as a where
  IxRZ :: IxR (a, b) b
  IxRS :: IxR a c -> IxR (a, b) c

deriving instance Show (IxR as a)
