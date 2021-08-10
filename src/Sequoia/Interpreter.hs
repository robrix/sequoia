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
import Data.Functor.Classes
import Sequoia.DeBruijn
import Sequoia.Snoc
import Text.Show (showListWith)

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
  | RNot (Scope Expr)
  | RNeg (Scope Expr)
  | L Expr (Elim Scope Expr)
  deriving (Show)

newtype Scope a = Scope { getScope :: a }
  deriving (Show)


-- Elimination

bindExpr :: ([a] -> Expr -> b) -> [a] -> Expr -> (a -> b)
bindExpr with env e a = with (a : env) e


-- Values

data Val
  = VNe Level (Snoc (Elim ((->) Val) Val))
  | VTop
  | VBottom
  | VOne
  | VWith Val Val
  | VSum1 Val
  | VSum2 Val
  | VNot (Val -> Val)
  | VNeg (Val -> Val)

instance Show Val where
  showsPrec = showsTerm 0


data Elim f a
  -- No rule for ETop
  = EZero
  | EBottom
  | EOne
  | EWith1 (f a)
  | EWith2 (f a)
  | ESum (f a) (f a)
  | ENot a
  | ENeg a

instance (ShowTerm1 f, ShowTerm a) => Show (Elim f a) where
  showsPrec = showsTerm 0


class ShowTerm a where
  showsTerm :: Level -> Int -> a -> ShowS

instance ShowTerm Expr where
  showsTerm _ = showsPrec

instance ShowTerm Val where
  showsTerm d p = \case
    VNe v sp  -> showsBinaryWith showsPrec (liftShowsPrec (showsTerm d) (showListWith (showsTerm d 0))) "VNe" p v sp
    VTop      -> showString "VTop"
    VBottom   -> showString "VBottom"
    VOne      -> showString "VOne"
    VWith a b -> showsBinaryWith (showsTerm d) (showsTerm d) "VWith" p a b
    VSum1 a   -> showsUnaryWith (showsTerm d) "VSum1" p a
    VSum2 b   -> showsUnaryWith (showsTerm d) "VSum2" p b
    VNot a    -> showsUnaryWith (liftShowsTerm showsTerm d) "VNot" p a
    VNeg a    -> showsUnaryWith (liftShowsTerm showsTerm d) "VNeg" p a

instance (ShowTerm1 f, ShowTerm a) => ShowTerm (Elim f a) where
  showsTerm d p = \case
    EZero    -> showString "EZero"
    EBottom  -> showString "EBottom"
    EOne     -> showString "EOne"
    EWith1 f -> showsUnaryWith (liftShowsTerm showsTerm d) "EWith1" p f
    EWith2 g -> showsUnaryWith (liftShowsTerm showsTerm d) "EWith2" p g
    ESum f g -> showsBinaryWith (liftShowsTerm showsTerm d) (liftShowsTerm showsTerm d) "ESum" p f g
    ENot v   -> showsUnaryWith (showsTerm d) "ENot" p v
    ENeg v   -> showsUnaryWith (showsTerm d) "ENeg" p v


class ShowTerm1 f where
  liftShowsTerm :: (Level -> Int -> a -> ShowS) -> Level -> Int -> f a -> ShowS

instance ShowTerm1 Scope where
  liftShowsTerm showsExpr d p = showsExpr d p . getScope

instance ShowTerm1 ((->) Val) where
  liftShowsTerm showsVal d p b = bindVal (flip . showsVal) d b p


-- Construction

vvar :: Level -> Val
vvar d = VNe d Nil

vapp :: Val -> Elim ((->) Val) Val -> Val
vapp = curry $ \case
  (v,         EZero)    -> v
  (VBottom,   EBottom)  -> VBottom
  (VOne,      EOne)     -> VOne
  (VWith a _, EWith1 f) -> f a
  (VWith _ b, EWith2 g) -> g b
  (VSum1 a,   ESum f _) -> f a
  (VSum2 b,   ESum _ g) -> g b
  (VNot k,    ENot a)   -> k a
  (VNeg k,    ENeg a)   -> k a
  (v,         e)        -> error $ "cannot elim " <> show v <> " with " <> show e


-- Elimination

bindVal :: (Level -> a -> b) -> Level -> (Val -> a) -> b
bindVal with d b = with (succ d) (b (vvar d))


-- Computation

mapElim :: (a -> b) -> (f a -> g b) -> (Elim f a -> Elim g b)
mapElim g h = \case
  EZero    -> EZero
  EBottom  -> EBottom
  EOne     -> EOne
  EWith1 f -> EWith1 (h f)
  EWith2 g -> EWith2 (h g)
  ESum f g -> ESum (h f) (h g)
  ENot a   -> ENot (g a)
  ENeg a   -> ENeg (g a)


-- Quotation

quoteVal :: Level -> Val -> Expr
quoteVal d = \case
  VNe v sp  -> foldl' ((. quoteElim d) . L) (Var (levelToIndex d v)) sp
  VTop      -> RTop
  VBottom   -> RBottom
  VOne      -> ROne
  VWith a b -> RWith (quoteVal d a) (quoteVal d b)
  VSum1 a   -> RSum1 (quoteVal d a)
  VSum2 b   -> RSum2 (quoteVal d b)
  VNot f    -> RNot (Scope (quoteBinder d f))
  VNeg f    -> RNeg (Scope (quoteBinder d f))

quoteElim :: Level -> Elim ((->) Val) Val -> Elim Scope Expr
quoteElim d = mapElim (quoteVal d) (Scope . quoteBinder d)

quoteBinder :: Level -> (Val -> Val) -> Expr
quoteBinder = bindVal quoteVal


-- Evaluation (definitional)

type Env = [Val]

evalDef :: Env -> Expr -> Val
evalDef env = \case
  Var v     -> env !! getIndex v
  RTop      -> VTop
  RBottom   -> VBottom
  ROne      -> VOne
  RWith a b -> VWith (evalDef env a) (evalDef env b)
  RSum1 a   -> VSum1 (evalDef env a)
  RSum2 b   -> VSum2 (evalDef env b)
  RNot f    -> VNot (evalBinder env (getScope f))
  RNeg f    -> VNeg (evalBinder env (getScope f))
  L s e     -> vapp (evalDef env s) (mapElim (evalDef env) (evalBinder env . getScope) e)

evalBinder :: Env -> Expr -> (Val -> Val)
evalBinder = bindExpr evalDef


-- Evaluation (CK machine)

type Cont = Snoc Frame

data Frame
  = FRWithL () Expr
  | FRWithR Val ()
  | FRSum1 ()
  | FRSum2 ()
  | FL (Elim Scope Expr)
  | FLZero
  | FLBottom
  | FLOne
  | FLWith1 (Scope Expr)
  | FLWith2 (Scope Expr)
  | FLSum (Scope Expr) (Scope Expr)
  | FLNotL () Expr
  | FLNotR Val ()
  | FLNegL () Expr
  | FLNegR Val ()

evalCK :: Env -> Expr -> Val
evalCK env e = load env e Nil

load :: Env -> Expr -> Cont -> Val
load env e k = case e of
  Var a     -> unload env (env !! getIndex a) k
  RTop      -> unload env VTop k
  RBottom   -> unload env VBottom k
  ROne      -> unload env VOne k
  RWith a b -> load env a (k :> FRWithL () b)
  RSum1 a   -> load env a (k :> FRSum1 ())
  RSum2 b   -> load env b (k :> FRSum2 ())
  RNot f    -> unload env (VNot (loadBinder env (getScope f) k)) k
  RNeg f    -> unload env (VNeg (loadBinder env (getScope f) k)) k
  L s e     -> load env s (k :> FL e)

loadBinder :: Env -> Expr -> Cont -> (Val -> Val)
loadBinder env f k a = bindExpr load env f a k

unload :: Env -> Val -> Cont -> Val
unload env v = \case
  Nil               -> v
  k :> FRWithL () r -> load env r (k :> FRWithR v ())
  k :> FRWithR u () -> unload env (VWith u v) k
  k :> FRSum1 ()    -> unload env (VSum1 v) k
  k :> FRSum2 ()    -> unload env (VSum2 v) k
  k :> FL e         -> unload env (case e of
    EZero    -> unload env (vapp v EZero) k
    EBottom  -> unload env (vapp v EBottom) k
    EOne     -> unload env (vapp v EOne) k
    EWith1 f -> unload env (vapp v (EWith1 (loadBinder env (getScope f) k))) k
    EWith2 g -> unload env (vapp v (EWith2 (loadBinder env (getScope g) k))) k
    ESum f g -> unload env (vapp v (ESum (loadBinder env (getScope f) k) (loadBinder env (getScope g) k))) k
    ENot r   -> load env r (k :> FLNotR v ())
    ENeg r   -> load env r (k :> FLNegR v ())) k
  k :> FLZero       -> unload env (vapp v EZero) k
  k :> FLBottom     -> unload env (vapp v EBottom) k
  k :> FLOne        -> unload env (vapp v EOne) k
  k :> FLWith1 f    -> unload env (vapp v (EWith1 (loadBinder env (getScope f) k))) k
  k :> FLWith2 g    -> unload env (vapp v (EWith2 (loadBinder env (getScope g) k))) k
  k :> FLSum f g    -> unload env (vapp v (ESum (loadBinder env (getScope f) k) (loadBinder env (getScope g) k))) k
  k :> FLNotL () r  -> load env r (k :> FLNotR v ())
  k :> FLNotR u ()  -> unload env (vapp v (ENot u)) k
  k :> FLNegL () r  -> load env r (k :> FLNegR v ())
  k :> FLNegR u ()  -> unload env (vapp v (ENeg u)) k
