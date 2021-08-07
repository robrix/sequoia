-- | Exponentials, represented as ¬A ⅋ ≁B.
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
import Sequoia.Connective.Not
import Sequoia.Connective.NotUntrue
import Sequoia.Profunctor
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Exponentials

newtype Exp env res a b = Exp { getExp :: forall res . (env ≁ b) • res -> (a ¬ res) • res -> res  }

instance Functor (Exp env res a) where
  fmap = rmap

instance Profunctor (Exp e r) where
  dimap f g (Exp r) = Exp (dimap (lmap (rmap g)) (lmap (lmap (lmap f))) r)


-- Construction

exp :: (forall res . (env ≁ b) • res -> a -> res) -> Exp env res a b
exp f = Exp (\ b a -> a • inK (f b))

exp' :: (a -> b) -> Exp env res a b
exp' f = exp (\ b a -> b • pure (f a))


-- Elimination

runExp :: Exp env res a b -> b • res -> a -> env ==> res
runExp (Exp r) k a = C (\ env -> r (k <<^ (env ∘)) (dn a))
