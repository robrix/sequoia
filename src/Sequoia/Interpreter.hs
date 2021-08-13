{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Direct-style and CPS interpreters for a small polarized calculus.
module Sequoia.Interpreter
( -- * Expressions
  Expr(..)
, EScope(..)
  -- * Values
, Val(..)
, Elim(..)
  -- ** Construction
, vvar
, vapp
  -- * Scopes
, Scope(..)
  -- * Quotation
, quoteVal
  -- * Evaluation (definitional)
, Env
, evalDef
  -- * Evaluation (CK machine)
, Cont
, Frame(..)
, evalCK
, load
, unload
) where

import Data.Foldable (foldl')
import Sequoia.DeBruijn
import Sequoia.Snoc

-- Expressions

data Expr
  = Var Index
  | RTop
  -- No rule for RZero
  | RBottom
  | ROne
  | RWith Expr Expr
  | RSum1 Expr
  | RSum2 Expr
  | RPar Expr Expr
  | RTensor Expr Expr
  | RNot (EScope Expr)
  | RNeg (EScope Expr)
  | L Expr (Elim EScope Expr)
  deriving (Show)

newtype EScope a = EScope { getEScope :: a }
  deriving (Show)


-- Values

data Val
  = VNe Level (Snoc (Elim ((->) Val) Val))
  | VTop
  | VBottom
  | VOne
  | VWith Val Val
  | VSum1 Val
  | VSum2 Val
  | VPar Val Val
  | VTensor Val Val
  | VNot (Val -> Val)
  | VNeg (Val -> Val)

instance Show Val where
  showsPrec p = showsPrec p . quoteVal 0


data Elim f a
  -- No rule for ETop
  = EZero
  | EBottom
  | EOne
  | EWith1 (f a)
  | EWith2 (f a)
  | ESum (f a) (f a)
  | EPar (f a) (f a)
  | ETensor (f (f a))
  | ENot a
  | ENeg a

deriving instance Show a => Show (Elim EScope a)

instance Show (Elim ((->) Val) Val) where
  showsPrec p = showsPrec @(Elim EScope Expr) p . bind quoteVal 0


-- Construction

vvar :: Level -> Val
vvar d = VNe d Nil

vapp :: Val -> Elim ((->) Val) Val -> Val
vapp = curry $ \case
  (v,           EZero)     -> v
  (VBottom,     EBottom)   -> VBottom
  (VOne,        EOne)      -> VOne
  (VWith a _,   EWith1 f)  -> f a
  (VWith _ b,   EWith2 g)  -> g b
  (VSum1 a,     ESum f _)  -> f a
  (VSum2 b,     ESum _ g)  -> g b
  (VTensor a b, ETensor f) -> f a b
  (VNot k,      ENot a)    -> k a
  (VNeg k,      ENeg a)    -> k a
  (v,           e)         -> error $ "cannot elim " <> show v <> " with " <> show e


-- Scopes

class Scope env g f | f g -> env where
  bind :: (env -> a -> b) -> (env -> f a -> g b)

instance Scope Level EScope ((->) Val) where
  bind with d b = EScope (with (succ d) (b (vvar d)))

instance Scope [a] ((->) a) EScope where
  bind with env (EScope e) a = with (a : env) e

instance Scope env g f => Scope env (Elim g) (Elim f) where
  bind tm env = \case
    EZero     -> EZero
    EBottom   -> EBottom
    EOne      -> EOne
    EWith1 f  -> EWith1 (bind tm env f)
    EWith2 f  -> EWith2 (bind tm env f)
    ESum f g  -> ESum (bind tm env f) (bind tm env g)
    EPar f g  -> EPar (bind tm env f) (bind tm env g)
    ETensor f -> ETensor (bind (bind tm) env f)
    ENot a    -> ENot (tm env a)
    ENeg a    -> ENeg (tm env a)


-- Quotation

quoteVal :: Level -> Val -> Expr
quoteVal d = \case
  VNe v sp    -> foldl' ((. bind quoteVal d) . L) (Var (levelToIndex d v)) sp
  VTop        -> RTop
  VBottom     -> RBottom
  VOne        -> ROne
  VWith a b   -> RWith (quoteVal d a) (quoteVal d b)
  VSum1 a     -> RSum1 (quoteVal d a)
  VSum2 b     -> RSum2 (quoteVal d b)
  VPar a b    -> RPar (quoteVal d a) (quoteVal d b)
  VTensor a b -> RTensor (quoteVal d a) (quoteVal d b)
  VNot f      -> RNot (bind quoteVal d f)
  VNeg f      -> RNeg (bind quoteVal d f)


-- Evaluation (definitional)

type Env = [Val]

evalDef :: Env -> Expr -> Val
evalDef env = \case
  Var v       -> env !! getIndex v
  RTop        -> VTop
  RBottom     -> VBottom
  ROne        -> VOne
  RWith a b   -> VWith (evalDef env a) (evalDef env b)
  RSum1 a     -> VSum1 (evalDef env a)
  RSum2 b     -> VSum2 (evalDef env b)
  RPar a b    -> VPar (evalDef env a) (evalDef env b)
  RTensor a b -> VTensor (evalDef env a) (evalDef env b)
  RNot f      -> VNot (bind evalDef env f)
  RNeg f      -> VNeg (bind evalDef env f)
  L s e       -> vapp (evalDef env s) (bind evalDef env e)


-- Evaluation (CK machine)

type Cont = Snoc Frame

data Frame
  = FRWithL () Expr
  | FRWithR Val ()
  | FRSum1 ()
  | FRSum2 ()
  | FRParL () Expr
  | FRParR Val ()
  | FRTensorL () Expr
  | FRTensorR Val ()
  | FL (Elim EScope Expr)
  | FLNotR Val ()
  | FLNegR Val ()
  deriving (Show)

evalCK :: Env -> Expr -> Val
evalCK = load Nil

load :: Cont -> Env -> Expr -> Val
load k env = \case
  Var a       -> unload k env (env !! getIndex a)
  RTop        -> unload k env VTop
  RBottom     -> unload k env VBottom
  ROne        -> unload k env VOne
  RWith a b   -> load (k :> FRWithL () b) env a
  RSum1 a     -> load (k :> FRSum1 ()) env a
  RSum2 b     -> load (k :> FRSum2 ()) env b
  RPar a b    -> load (k :> FRParL () b) env a
  RTensor a b -> load (k :> FRTensorL () b) env a
  RNot f      -> unload k env (VNot (bind (load k) env f))
  RNeg f      -> unload k env (VNeg (bind (load k) env f))
  L s e       -> load (k :> FL e) env s

unload :: Cont -> Env -> (Val -> Val)
unload k env v = case k of
  Nil                 -> v
  k :> FRWithL () r   -> load (k :> FRWithR v ()) env r
  k :> FRWithR u ()   -> unload k env (VWith u v)
  k :> FRSum1 ()      -> unload k env (VSum1 v)
  k :> FRSum2 ()      -> unload k env (VSum2 v)
  k :> FRParL () r    -> load (k :> FRParR v ()) env r
  k :> FRParR u ()    -> unload k env (VPar u v)
  k :> FRTensorL () r -> load (k :> FRTensorR v ()) env r
  k :> FRTensorR u () -> unload k env (VTensor u v)
  k :> FL e           -> unload k env (case e of
    EZero     -> unload k env (vapp v EZero)
    EBottom   -> unload k env (vapp v EBottom)
    EOne      -> unload k env (vapp v EOne)
    EWith1 f  -> unload k env (vapp v (EWith1 (bind (load k) env f)))
    EWith2 g  -> unload k env (vapp v (EWith2 (bind (load k) env g)))
    ESum f g  -> unload k env (vapp v (ESum (bind (load k) env f) (bind (load k) env g)))
    EPar f g  -> unload k env (vapp v (EPar (bind (load k) env f) (bind (load k) env g)))
    ETensor f -> unload k env (vapp v (ETensor (bind (bind (load k)) env f)))
    ENot r    -> load (k :> FLNotR v ()) env r
    ENeg r    -> load (k :> FLNegR v ()) env r)
  k :> FLNotR u ()    -> unload k env (vapp v (ENot u))
  k :> FLNegR u ()    -> unload k env (vapp v (ENeg u))
