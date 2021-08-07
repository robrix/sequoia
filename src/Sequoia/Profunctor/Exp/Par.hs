module Sequoia.Profunctor.Exp.Par
( -- * Exponentials
  Exp(..)
  -- * Construction
, exp'
  -- * Elimination
, runExp
) where

import Data.Bifunctor
import Sequoia.Calculus.Not
import Sequoia.Calculus.NotUntrue
import Sequoia.Connective.Par.Parameterized
import Sequoia.Profunctor
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Exponentials

newtype Exp env res a b = Exp { getExp :: Par res (a ¬ res) (env ≁ b) }
  deriving (Functor)

instance Profunctor (Exp e r) where
  dimap f g = Exp . bimap (lmap f) (rmap g) . getExp


-- Construction

exp' :: (a -> b) -> Exp env res a b
exp' f = Exp (Par (K (\ (ka, kb) -> ka • Not (K (\ a -> kb • pure (f a))))))


-- Elimination

runExp :: Exp env res a b -> b • res -> a -> env ==> res
runExp (Exp (Par (K r))) k a = C (\ env -> r (dn a <<^ getNot, K (\ b -> k • env ∘ runNotUntrue b)))
