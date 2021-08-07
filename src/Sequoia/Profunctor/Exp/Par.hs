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

import Data.Bifunctor
import Prelude hiding (exp)
import Sequoia.Calculus.Par
import Sequoia.Connective.Not
import Sequoia.Disjunction
import Sequoia.Profunctor
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Exponentials

newtype Exp env res a b = Exp { getExp :: ((a ¬ res) ⅋ (env ∘ b)) •• res }

instance Functor (Exp env res a) where
  fmap = rmap

instance Profunctor (Exp e r) where
  dimap f g = Exp . lmap (lmap (bimap (lmap f) (rmap g))) . getExp


-- Construction

exp :: (a -> (env ∘ b) • res -> res) -> Exp env res a b
exp f = Exp (K (\ k -> inlL k • inK (\ a -> f a (inrL k))))

exp' :: (a -> b) -> Exp env res a b
exp' f = exp (\ a kb -> kb • pure (f a))


-- Elimination

runExp :: Exp env res a b -> b • res -> a -> env ==> res
runExp (Exp r) k a = C (\ env -> r • (dn a <••> K (\ b -> k • env ∘ b)))
