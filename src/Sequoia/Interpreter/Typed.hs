{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
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
, type (|-)(..)
, getE
, (<!)
, IxL(..)
, E
, (!>)
, IxR(..)
, R
, LvL(..)
) where

import Data.Functor.Classes
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

data Term binder ctx a where
  TVar :: IxL a _Γ -> Term binder ctx a
  TTop :: Term binder ctx Top
  TWith :: Term binder ctx a -> Term binder ctx b -> Term binder ctx (a & b)
  TSum1 :: Term binder ctx a -> Term binder ctx (a ⊕ b)
  TSum2 :: Term binder ctx b -> Term binder ctx (a ⊕ b)
  TBot :: Term binder (as |- bs) _Δ -> Term binder (as |- bs) (_Δ `Either` Bottom (R bs))
  TOne :: Term binder (as |- bs) (One (E as))
  TFun :: binder _Γ _Δ a b -> Term binder (_Γ |- _Δ) (a -> b)
  TNot :: Coterm binder ctx a -> Term binder ctx (Not a r)

instance Show2 (binder _Γ _Δ) => Show (Term binder (_Γ |- _Δ) a) where
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

deriving instance Show2 (binder _Γ _Δ) => Show (Coterm binder (_Γ |- _Δ) a)


newtype FO _Γ _Δ a b = FO (Term FO ((a, _Γ) |- _Δ) b)

instance Show2 (FO _Γ _Δ) where
  liftShowsPrec2 _ _ _ _ p (FO t) = showsUnaryWith showsPrec "FO" p t


class ShowTerm t where
  showsTerm :: Level -> Int -> t a -> ShowS

instance ShowBinder binder => ShowTerm (Term binder (_Γ |- _Δ)) where
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

instance ShowBinder binder => ShowTerm (Coterm binder (_Γ |- _Δ)) where
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
  showsBinder :: Level -> Int -> t _Γ _Δ a b -> ShowS

instance ShowBinder FO where
  showsBinder d p (FO t) = showsUnaryWith (showsTerm (succ d)) "FO" p t


-- Expressions

data Expr ctx a where
  Var :: IxL a as -> Expr (as |- bs) a
  RTop :: Expr ctx Top
  RWith :: Expr ctx a -> Expr ctx b -> Expr ctx (a & b)
  RSum1 :: Expr ctx a -> Expr ctx (a ⊕ b)
  RSum2 :: Expr ctx b -> Expr ctx (a ⊕ b)
  RBot :: Expr (as |- bs) _Δ -> Expr (as |- bs) (Either _Δ (Bottom (R bs)))
  ROne :: Expr (as |- bs) (One (E as))
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

newtype Scope as bs a b = Scope { getScope :: Expr ((a, as) |- bs) b }
  deriving (Show)


-- Values

data Val ctx a where
  VTop :: Val ctx Top
  VWith :: Val ctx a -> Val ctx b -> Val ctx (a & b)
  VSum1 :: Val ctx a -> Val ctx (a ⊕ b)
  VSum2 :: Val ctx b -> Val ctx (a ⊕ b)
  VBottom :: Val (as |- bs) (Bottom (R bs))
  VOne :: Val (as |- bs) (One (E as))
  VFun :: (Val (as |- bs) a -> Val ((a, as) |- bs) b) -> Val (as |- bs) (a -> b)

data Coval ctx a where
  EZero :: Coval ctx Zero
  EWith1 :: Coval ctx a -> Coval ctx (a & b)
  EWith2 :: Coval ctx b -> Coval ctx (a & b)
  ESum :: Coval ctx a -> Coval ctx b -> Coval ctx (a ⊕ b)
  EBottom :: Coval (as |- bs) (Bottom (R bs))
  EOne :: Coval (as |- bs) a -> Coval (as |- bs) (One (E as), a)
  EFun :: Val ctx a -> Coval ctx b -> Coval ctx (a -> b)


-- Definitional interpreter

evalDef :: as |- bs -> Expr (as |- bs) a -> a
evalDef ctx = \case
  Var i     -> i <! ctx
  RTop      -> Top
  RWith a b -> evalDef ctx a >--< evalDef ctx b
  RSum1 a   -> InL (evalDef ctx a)
  RSum2 b   -> InR (evalDef ctx b)
  RBot a    -> Left (evalDef ctx a)
  ROne      -> One (getE ctx)
  RFun b    -> \ a -> evalDef (a :<< ctx) (getScope b)

coevalDef :: as |- bs -> Coexpr (as |- bs) a -> (a -> R bs)
coevalDef ctx = \case
  Covar i  -> ctx !> i
  LZero    -> absurdP
  LWith1 a -> coevalDef ctx a . exl
  LWith2 b -> coevalDef ctx b . exr
  LSum l r -> coevalDef ctx l <--> coevalDef ctx r
  LBot     -> absurdN
  LOne a   -> coevalDef ctx a . snd
  LFun a b -> \ f -> coevalDef ctx b (f (evalDef ctx a))


-- Environments

data a |- b where
  ΓΔ :: e -> One e |- Bottom r
  (:<<) :: a -> as |- bs -> (a, as) |- bs
  (:>>) :: as |- bs -> (b -> R bs) -> as |- (bs, b)

infix 3 |-
infixr 5 :<<
infixl 5 :>>

getE :: as |- bs -> E as
getE = \case
  ΓΔ e    -> e
  _ :<< s -> getE s
  s :>> _ -> getE s


(<!) :: IxL a as -> as |- bs -> a
i      <! (c :>> _) = i <! c
IxLZ   <! (h :<< _) = h
IxLS i <! (_ :<< c) = i <! c

infixr 2 <!

data IxL a as where
  IxLZ :: IxL a (a, b)
  IxLS :: IxL c b -> IxL c (a, b)

deriving instance Show (IxL as a)

type family E ctx where
  E (_, as) = E as
  E (One e) = e


(!>) :: as |- bs -> IxR bs b -> (b -> R bs)
delta !> ix = case (ix, delta) of
  (i,      _ :<< c) -> c !> i
  (IxRZ,   _ :>> r) -> r
  (IxRS i, c :>> _) -> c !> i

infixl 2 !>

data IxR as a where
  IxRZ :: IxR (a, b) b
  IxRS :: IxR a c -> IxR (a, b) c

deriving instance Show (IxR as a)

type family R ctx where
  R (bs, _)    = R bs
  R (Bottom r) = r


data LvL a as where
  LvLZ :: LvL (One e) (One e)
  LvLS :: LvL a as -> LvL b (b, as)
