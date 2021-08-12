{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Interpreter.Typed
( -- * Expressions
  Src(..)
, Snk
, absurdSnk
, Expr
  -- * Values
, Val
  -- * Quotation
, quoteVal
  -- * Evaluator
, eval
, coeval
, copure
, evaluator
, evaluator'
, evalFun
, (<<>>)
  -- * Definitional interpreter
, evalDef
  -- * Execution
, execVal
) where

import Control.Category (Category, (>>>))
import Prelude hiding (exp)
import Sequoia.Connective.Function
import Sequoia.Disjunction
import Sequoia.Monad.Run
import Sequoia.Profunctor
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exp hiding (Coexp(..))

-- Expressions

data Src = Src
data Snk

absurdSnk :: Snk -> a
absurdSnk = \case

data Expr e r a b where

deriving instance Show (Expr e r a b)


-- Values

data Val e r a b where


-- Quotation

quoteVal :: Val e r a b -> Expr e r a b
quoteVal = \case


-- Evaluator

eval :: Eval e r a b -> (b • r) -> a • r
eval = getExp . getEval

coeval :: Eval e r a r -> (a • r)
coeval = (`eval` idK)

copure :: (a • r) -> Eval e r a r
copure = evaluator . (>>>)

evaluator :: ((b • r) -> (a • r)) -> Eval e r a b
evaluator = Eval . Exp

evaluator' :: (a -> b) -> Eval e r a b
evaluator' = evaluator . (^>>)

evalFun :: Fun r a b -> Eval e r a b
evalFun = Eval . runFunExp

(<<>>) :: Disj d => Eval e r a s -> Eval e r b s -> Eval e r (a `d` b) s
f <<>> g = evaluator (\ k -> eval f k <••> eval g k)

infix 3 <<>>

newtype Eval e r a b = Eval { getEval :: Exp r a b }
  deriving (Applicative, Category, Functor, Monad, MonadRunK r, Profunctor)


-- Definitional interpreter

evalDef :: Expr e r a b -> Eval e r a b
evalDef = \case


-- Execution

execVal :: Val e r a b -> Eval e r a b
execVal = \case
