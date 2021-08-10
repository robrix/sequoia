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
, IxL(..)
, IxR(..)
) where

import Data.Void
import Sequoia.Conjunction
import Sequoia.Connective.Sum
import Sequoia.Connective.With
import Sequoia.Disjunction

-- Expressions

data Expr as bs a where
  Var :: IxL a as -> Expr as bs a
  RWith :: Expr as bs a -> Expr as bs b -> Expr as bs (a & b)
  RSum1 :: Expr as bs a -> Expr as bs (a ⊕ b)
  RSum2 :: Expr as bs b -> Expr as bs (a ⊕ b)
  RBot :: Expr as bs _Δ -> Expr as bs (Either _Δ Void)
  ROne :: Expr as bs ()
  RFun :: Scope as bs a b -> Expr as bs (a -> b)

deriving instance Show (Expr as bs a)

data Coexpr as bs a where
  Covar :: IxR bs a -> Coexpr as bs a
  LSum :: Coexpr as bs a -> Coexpr as bs b -> Coexpr as bs (a ⊕ b)
  LBot :: Coexpr as bs Void
  LOne :: Coexpr as bs  _Γ -> Coexpr as bs  ((), _Γ)
  LFun :: Expr as bs a -> Coexpr as bs  b -> Coexpr as bs  (a -> b)

deriving instance Show (Coexpr as bs a)

newtype Scope as bs a b = Scope { getScope :: Expr (a, as) bs b }
  deriving (Show)


-- Definitional interpreter

evalDef :: Γ as |- Δ r bs -> Expr as bs a -> a
evalDef ctx@(_Γ :|-: _Δ) = \case
  Var i     -> i <! _Γ
  RWith a b -> evalDef ctx a >--< evalDef ctx b
  RSum1 a   -> InL (evalDef ctx a)
  RSum2 b   -> InR (evalDef ctx b)
  RBot a    -> Left (evalDef ctx a)
  ROne      -> ()
  RFun b    -> \ a -> evalDef (a :< _Γ :|-: _Δ) (getScope b)

coevalDef :: Γ as |- Δ r bs -> Coexpr as bs a -> (a -> r)
coevalDef ctx@(_ :|-: _Δ) = \case
  Covar i  -> _Δ !> i
  LSum l r -> coevalDef ctx l <--> coevalDef ctx r
  LBot     -> absurd
  LOne a   -> coevalDef ctx a . snd
  LFun a b -> \ f -> coevalDef ctx b (f (evalDef ctx a))


-- Environments

data Γ as where
  Γ :: Γ ()
  (:<) :: a -> Γ b -> Γ (a, b)

infixr 5 :<

(<!) :: IxL a as -> Γ as -> a
IxLZ   <! (h :< _) = h
IxLS i <! (_ :< t) = i <! t


data Δ r as where
  Δ :: r -> Δ r Void
  (:>) :: Δ r a -> (b -> r) -> Δ r (a, b)

infixl 5 :>

(!>) :: Δ r as -> IxR as a -> (a -> r)
delta !> ix = case (ix, delta) of
  (IxRZ,   _ :> r) -> r
  (IxRS i, l :> _) -> l !> i


data a :|-: b = a :|-: b

infix 2 :|-:, |-

type (|-) = (:|-:)

(|-) :: a -> b -> a |- b
(|-) = (:|-:)


data IxL a as where
  IxLZ :: IxL a (a, b)
  IxLS :: IxL c b -> IxL c (a, b)

deriving instance Show (IxL as a)

data IxR as a where
  IxRZ :: IxR (a, b) b
  IxRS :: IxR a c -> IxR (a, b) c

deriving instance Show (IxR as a)
