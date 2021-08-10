{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Sequoia.Interpreter.Typed
( -- * Expressions
  Expr(..)
, Coexpr(..)
, Scope(..)
  -- * Definitional interpreter
, evalDef
, coevalDef
  -- * Environments
, Γ(..)
, (<!)
, Δ(..)
, (!>)
, (:|-:)(..)
, type (|-)
, (|-)
, Ix(..)
) where

import Data.Void

-- Expressions

data Expr as bs a where
  Var :: Ix as a -> Expr as bs a
  RBot :: Expr as bs _Δ -> Expr as bs (Either _Δ Void)
  ROne :: Expr as bs ()
  RFun :: Scope as bs a b -> Expr as bs (a -> b)

deriving instance Show (Expr as bs a)

data Coexpr as bs a where
  Covar :: Ix bs a -> Coexpr as bs a
  LBot :: Coexpr as bs Void
  LOne :: Coexpr as bs  _Γ -> Coexpr as bs  ((), _Γ)
  LFun :: Expr as bs a -> Coexpr as bs  b -> Coexpr as bs  (a -> b)

deriving instance Show (Coexpr as bs a)

newtype Scope as bs a b = Scope { getScope :: Expr (as, a) bs b }
  deriving (Show)


-- Definitional interpreter

evalDef :: Γ as |- Δ r bs -> Expr as bs a -> a
evalDef ctx@(_Γ :|-: _Δ) = \case
  Var i  -> i <! _Γ
  RBot a -> Left (evalDef ctx a)
  ROne   -> ()
  RFun b -> \ a -> evalDef (a :< _Γ :|-: _Δ) (getScope b)

coevalDef :: Γ as |- Δ r bs -> Coexpr as bs a -> (a -> r)
coevalDef ctx@(_ :|-: _Δ) = \case
  Covar i  -> _Δ !> i
  LBot     -> absurd
  LOne a   -> coevalDef ctx a . snd
  LFun a b -> \ f -> coevalDef ctx b (f (evalDef ctx a))


-- Environments

type (*) = (,)


data Γ as where
  Γ :: Γ ()
  (:<) :: a -> Γ b -> Γ (b * a)

infixr 5 :<

(<!) :: Ix as a -> Γ as -> a
IxZ   <! (h :< _) = h
IxS i <! (_ :< t) = i <! t


data Δ r as where
  Δ :: r -> Δ r Void
  (:>) :: Δ r a -> (b -> r) -> Δ r (a * b)

infixl 5 :>

(!>) :: Δ r as -> Ix as a -> (a -> r)
delta !> ix = case (ix, delta) of
  (IxZ,   _ :> r) -> r
  (IxS i, l :> _) -> l !> i


data a :|-: b = a :|-: b

infix 2 :|-:, |-

type (|-) = (:|-:)

(|-) :: a -> b -> a |- b
(|-) = (:|-:)


data Ix as a where
  IxZ :: Ix (a * b) b
  IxS :: Ix a c -> Ix (a * b) c

deriving instance Show (Ix as a)
