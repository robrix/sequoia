module Sequoia.Profunctor.Exp.Par
( -- * Exponentials
  Exp(..)
  -- * Construction
, exp
, exp'
  -- * Elimination
, runExp
) where

import Data.Bifunctor
import Prelude hiding (exp)
import Sequoia.Calculus.NotUntrue
import Sequoia.Profunctor
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Exponentials

newtype Exp env res a b = Exp { getExp :: (a, (env ≁ b) • res) -> res }

instance Functor (Exp env res a) where
  fmap = rmap

instance Profunctor (Exp e r) where
  dimap f g = Exp . lmap (bimap f (lmap (rmap g))) . getExp


-- Construction

exp :: (a -> (env ≁ b) • res -> res) -> Exp env res a b
exp = Exp . uncurry

exp' :: (a -> b) -> Exp env res a b
exp' f = Exp (\ (a, kb) -> kb • NotUntrue (pure (f a)))


-- Elimination

runExp :: Exp env res a b -> b • res -> a -> env ==> res
runExp (Exp r) k a = C (\ env -> r (a, K (\ b -> k • env ∘ runNotUntrue b)))
