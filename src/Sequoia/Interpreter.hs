-- | Direct-style and CPS interpreters for a small polarized calculus.
module Sequoia.Interpreter
( -- * Expressions
  Expr(..)
, Scope(..)
  -- ** Elimination
, bindExpr
  -- * Values
, Val(..)
, Elim(..)
  -- ** Construction
, vvar
, vapp
  -- ** Elimination
, bindVal
  -- ** Computation
, mapElim
  -- * Quotation
, quoteVal
, quoteElim
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
  | RNot (Scope Expr)
  | RNeg (Scope Expr)
  | L Expr (Elim Scope Expr)
  deriving (Show)

newtype Scope a = Scope { getScope :: a }
  deriving (Show)


-- Elimination

bindExpr :: ([a] -> Expr -> b) -> [a] -> Scope Expr -> (a -> b)
bindExpr with env e a = with (a : env) (getScope e)

bindExpr2 :: ([a] -> Expr -> b) -> [a] -> Scope (Scope Expr) -> (a -> a -> b)
bindExpr2 with env e a b = with (a : b : env) (getScope (getScope e))


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

deriving instance Show a => Show (Elim Scope a)

instance Show (Elim ((->) Val) Val) where
  showsPrec p = showsPrec p . quoteElim 0


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


-- Elimination

bindVal :: (Level -> a -> b) -> Level -> (Val -> a) -> b
bindVal with d b = with (succ d) (b (vvar d))


-- Computation

mapElim :: (a -> b) -> (f a -> g b) -> (f (f a) -> g (g b)) -> (Elim f a -> Elim g b)
mapElim tm sc sc2 = \case
  EZero     -> EZero
  EBottom   -> EBottom
  EOne      -> EOne
  EWith1 f  -> EWith1 (sc f)
  EWith2 f  -> EWith2 (sc f)
  ESum f g  -> ESum (sc f) (sc g)
  EPar f g  -> EPar (sc f) (sc g)
  ETensor f -> ETensor (sc2 f)
  ENot a    -> ENot (tm a)
  ENeg a    -> ENeg (tm a)


-- Quotation

quoteVal :: Level -> Val -> Expr
quoteVal d = \case
  VNe v sp    -> foldl' ((. quoteElim d) . L) (Var (levelToIndex d v)) sp
  VTop        -> RTop
  VBottom     -> RBottom
  VOne        -> ROne
  VWith a b   -> RWith (quoteVal d a) (quoteVal d b)
  VSum1 a     -> RSum1 (quoteVal d a)
  VSum2 b     -> RSum2 (quoteVal d b)
  VPar a b    -> RPar (quoteVal d a) (quoteVal d b)
  VTensor a b -> RTensor (quoteVal d a) (quoteVal d b)
  VNot f      -> RNot (quoteBinder d f)
  VNeg f      -> RNeg (quoteBinder d f)

quoteElim :: Level -> Elim ((->) Val) Val -> Elim Scope Expr
quoteElim d = mapElim (quoteVal d) (quoteBinder d) (quoteBinder2 d)

quoteBinder :: Level -> (Val -> Val) -> Scope Expr
quoteBinder = fmap Scope . bindVal quoteVal

quoteBinder2 :: Level -> (Val -> Val -> Val) -> Scope (Scope Expr)
quoteBinder2 = fmap (Scope . Scope) . bindVal (bindVal quoteVal)


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
  RNot f      -> VNot (evalBinder env f)
  RNeg f      -> VNeg (evalBinder env f)
  L s e       -> vapp (evalDef env s) (mapElim (evalDef env) (evalBinder env) (evalBinder2 env) e)

evalBinder :: Env -> Scope Expr -> (Val -> Val)
evalBinder = bindExpr evalDef

evalBinder2 :: Env -> Scope (Scope Expr) -> (Val -> Val -> Val)
evalBinder2 = bindExpr2 evalDef


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
  | FL (Elim Scope Expr)
  | FLNotR Val ()
  | FLNegR Val ()
  deriving (Show)

evalCK :: Env -> Expr -> Val
evalCK env e = load env e Nil

load :: Env -> Expr -> Cont -> Val
load env e k = case e of
  Var a       -> unload env (env !! getIndex a) k
  RTop        -> unload env VTop k
  RBottom     -> unload env VBottom k
  ROne        -> unload env VOne k
  RWith a b   -> load env a (k :> FRWithL () b)
  RSum1 a     -> load env a (k :> FRSum1 ())
  RSum2 b     -> load env b (k :> FRSum2 ())
  RPar a b    -> load env a (k :> FRParL () b)
  RTensor a b -> load env a (k :> FRTensorL () b)
  RNot f      -> unload env (VNot (loadBinder env f k)) k
  RNeg f      -> unload env (VNeg (loadBinder env f k)) k
  L s e       -> load env s (k :> FL e)

loadBinder :: Env -> Scope Expr -> Cont -> (Val -> Val)
loadBinder env f k a = bindExpr load env f a k

loadBinder2 :: Env -> Scope (Scope Expr) -> Cont -> (Val -> Val -> Val)
loadBinder2 env f k a b = bindExpr2 load env f a b k

unload :: Env -> Val -> Cont -> Val
unload env v = \case
  Nil                 -> v
  k :> FRWithL () r   -> load env r (k :> FRWithR v ())
  k :> FRWithR u ()   -> unload env (VWith u v) k
  k :> FRSum1 ()      -> unload env (VSum1 v) k
  k :> FRSum2 ()      -> unload env (VSum2 v) k
  k :> FRParL () r    -> load env r (k :> FRParR v ())
  k :> FRParR u ()    -> unload env (VPar u v) k
  k :> FRTensorL () r -> load env r (k :> FRTensorR v ())
  k :> FRTensorR u () -> unload env (VTensor u v) k
  k :> FL e           -> unload env (case e of
    EZero     -> unload env (vapp v EZero) k
    EBottom   -> unload env (vapp v EBottom) k
    EOne      -> unload env (vapp v EOne) k
    EWith1 f  -> unload env (vapp v (EWith1 (loadBinder env f k))) k
    EWith2 g  -> unload env (vapp v (EWith2 (loadBinder env g k))) k
    ESum f g  -> unload env (vapp v (ESum (loadBinder env f k) (loadBinder env g k))) k
    EPar f g  -> unload env (vapp v (EPar (loadBinder env f k) (loadBinder env g k))) k
    ETensor f -> unload env (vapp v (ETensor (loadBinder2 env f k))) k
    ENot r    -> load env r (k :> FLNotR v ())
    ENeg r    -> load env r (k :> FLNegR v ())) k
  k :> FLNotR u ()    -> unload env (vapp v (ENot u)) k
  k :> FLNegR u ()    -> unload env (vapp v (ENeg u)) k
