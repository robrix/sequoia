module Sequoia.Profunctor.Exp.Par
( -- * Exponentials
  Exp(..)
  -- * Construction
, exp
, exp'
  -- * Elimination
, runExp
) where

import Prelude hiding (exp)
import Sequoia.Profunctor
import Sequoia.Profunctor.Context

-- Exponentials

newtype Exp env res a b = Exp { getExp :: a -> ((env -> b) -> res) -> res }

instance Functor (Exp env res a) where
  fmap = rmap

instance Profunctor (Exp e r) where
  dimap f g = Exp . dimap f (lmap (lmap (rmap g))) . getExp


-- Construction

exp :: (a -> ((env -> b) -> res) -> res) -> Exp env res a b
exp = Exp

exp' :: (a -> b) -> Exp env res a b
exp' f = Exp (\ a kb -> kb (pure (f a)))


-- Elimination

runExp :: Exp env res a b -> (b -> res) -> a -> env ==> res
runExp (Exp r) k a = C (\ env -> r a (\ b -> k (b env)))
