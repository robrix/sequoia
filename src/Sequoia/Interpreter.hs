-- | Direct-style and CPS interpreters for a small polarized calculus.
module Sequoia.Interpreter
( -- * Expressions
  Expr(..)
, Scope(..)
  -- * Values
, Val(..)
, Elim(..)
  -- ** Construction
, vvar
, vapp
  -- ** Elimination
, showsVal
, showsElim
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
  -- No rule for LTop
  | LZero Expr
  | LBottom Expr
  | LOne Expr
  | LWith1 Expr (Scope Expr)
  | LWith2 Expr (Scope Expr)
  | LSum Expr (Scope Expr) (Scope Expr)
  | LNot Expr Expr
  | LNeg Expr Expr
  deriving (Show)

newtype Scope a = Scope { getScope :: a }
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
  | VNot (Val -> Val)
  | VNeg (Val -> Val)

instance Show Val where
  showsPrec = showsVal 0


data Elim f a
  = EZero
  | EBottom
  | EOne
  | EWith1 (f a)
  | EWith2 (f a)
  | ESum (f a) (f a)
  | ENot a
  | ENeg a

instance Show (Elim ((->) Val) Val) where
  showsPrec = showsElim 0


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

showsVal :: Level -> Int -> Val -> ShowS
showsVal d p = \case
  VNe v sp  -> showsBinaryWith showsPrec (liftShowsPrec (showsElim d) (showListWith (showsElim d 0))) "VNe" p v sp
  VTop      -> showString "VTop"
  VBottom   -> showString "VBottom"
  VOne      -> showString "VOne"
  VWith a b -> showsBinaryWith (showsVal d) (showsVal d) "VWith" p a b
  VSum1 a   -> showsUnaryWith (showsVal d) "VSum1" p a
  VSum2 b   -> showsUnaryWith (showsVal d) "VSum2" p b
  VNot a    -> showsUnaryWith (showsBinder d) "VNot" p a
  VNeg a    -> showsUnaryWith (showsBinder d) "VNeg" p a

showsElim :: Level -> Int -> Elim ((->) Val) Val -> ShowS
showsElim d p = \case
  EZero    -> showString "EZero"
  EBottom  -> showString "EBottom"
  EOne     -> showString "EOne"
  EWith1 f -> showsUnaryWith (showsBinder d) "EWith1" p f
  EWith2 g -> showsUnaryWith (showsBinder d) "EWith2" p g
  ESum f g -> showsBinaryWith (showsBinder d) (showsBinder d) "ESum" p f g
  ENot v   -> showsUnaryWith (showsVal d) "ENot" p v
  ENeg v   -> showsUnaryWith (showsVal d) "ENeg" p v

showsBinder :: Level -> Int -> (Val -> Val) -> ShowS
showsBinder d p b = showsVal (succ d) p (b (vvar d))


-- Quotation

quoteVal :: Level -> Val -> Expr
quoteVal d = \case
  VNe v sp  -> foldl' (quoteElim d) (Var (levelToIndex d v)) sp
  VTop      -> RTop
  VBottom   -> RBottom
  VOne      -> ROne
  VWith a b -> RWith (quoteVal d a) (quoteVal d b)
  VSum1 a   -> RSum1 (quoteVal d a)
  VSum2 b   -> RSum2 (quoteVal d b)
  VNot f    -> RNot (quoteBinder d f)
  VNeg f    -> RNeg (quoteBinder d f)

quoteElim :: Level -> Expr -> Elim ((->) Val) Val -> Expr
quoteElim d s = \case
  EZero    -> LZero s
  EBottom  -> LBottom s
  EOne     -> LOne s
  EWith1 f -> LWith1 s (quoteBinder d f)
  EWith2 g -> LWith2 s (quoteBinder d g)
  ESum f g -> LSum s (quoteBinder d f) (quoteBinder d g)
  ENot v   -> LNot s (quoteVal d v)
  ENeg v   -> LNeg s (quoteVal d v)

quoteBinder :: Level -> (Val -> Val) -> Scope Expr
quoteBinder d f = Scope (quoteVal (succ d) (f (vvar d)))


-- Evaluation (definitional)

type Env = [Val]

evalDef :: Env -> Expr -> Val
evalDef env = \case
  Var v      -> env !! getIndex v
  RTop       -> VTop
  RBottom    -> VBottom
  ROne       -> VOne
  RWith a b  -> VWith (evalDef env a) (evalDef env b)
  RSum1 a    -> VSum1 (evalDef env a)
  RSum2 b    -> VSum2 (evalDef env b)
  RNot f     -> VNot (evalBinder env f)
  RNeg f     -> VNeg (evalBinder env f)
  LZero s    -> vapp (evalDef env s) EZero
  LBottom s  -> vapp (evalDef env s) EBottom
  LOne s     -> vapp (evalDef env s) EOne
  LWith1 s f -> vapp (evalDef env s) (EWith1 (evalBinder env f))
  LWith2 s g -> vapp (evalDef env s) (EWith2 (evalBinder env g))
  LSum s f g -> vapp (evalDef env s) (ESum (evalBinder env f) (evalBinder env g))
  LNot s v   -> vapp (evalDef env s) (ENot (evalDef env v))
  LNeg s v   -> vapp (evalDef env s) (ENeg (evalDef env v))

evalBinder :: Env -> Scope Expr -> (Val -> Val)
evalBinder env (Scope e) a = evalDef (a : env) e


-- Evaluation (CK machine)

type Cont = Snoc Frame

data Frame
  = FRWithL () Expr
  | FRWithR Val ()
  | FRSum1 ()
  | FRSum2 ()
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
  Var a      -> unload env (env !! getIndex a) k
  RTop       -> unload env VTop k
  RBottom    -> unload env VBottom k
  ROne       -> unload env VOne k
  RWith a b  -> load env a (k :> FRWithL () b)
  RSum1 a    -> load env a (k :> FRSum1 ())
  RSum2 b    -> load env b (k :> FRSum2 ())
  RNot f     -> unload env (VNot (loadBinder env f k)) k
  RNeg f     -> unload env (VNeg (loadBinder env f k)) k
  LZero s    -> load env s (k :> FLZero)
  LBottom s  -> load env s (k :> FLBottom)
  LOne s     -> load env s (k :> FLOne)
  LWith1 s f -> load env s (k :> FLWith1 f)
  LWith2 s g -> load env s (k :> FLWith2 g)
  LSum s f g -> load env s (k :> FLSum f g)
  LNot s v   -> load env s (k :> FLNotL () v)
  LNeg s v   -> load env s (k :> FLNegL () v)

loadBinder :: Env -> Scope Expr -> Cont -> (Val -> Val)
loadBinder env (Scope f) k a = load (a : env) f k

unload :: Env -> Val -> Cont -> Val
unload env v = \case
  Nil               -> v
  k :> FRWithL () r -> load env r (k :> FRWithR v ())
  k :> FRWithR u () -> unload env (VWith u v) k
  k :> FRSum1 ()    -> unload env (VSum1 v) k
  k :> FRSum2 ()    -> unload env (VSum2 v) k
  k :> FLZero       -> unload env (vapp v EZero) k
  k :> FLBottom     -> unload env (vapp v EBottom) k
  k :> FLOne        -> unload env (vapp v EOne) k
  k :> FLWith1 f    -> unload env (vapp v (EWith1 (loadBinder env f k))) k
  k :> FLWith2 g    -> unload env (vapp v (EWith2 (loadBinder env g k))) k
  k :> FLSum f g    -> unload env (vapp v (ESum (loadBinder env f k) (loadBinder env g k))) k
  k :> FLNotL () r  -> load env r (k :> FLNotR v ())
  k :> FLNotR u ()  -> unload env (vapp v (ENot u)) k
  k :> FLNegL () r  -> load env r (k :> FLNegR v ())
  k :> FLNegR u ()  -> unload env (vapp v (ENeg u)) k