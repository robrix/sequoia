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

newtype Exp env res a b = Exp { getExp :: forall res . (a ¬ res) • res -> (env ≁ b) • res -> res  }

instance Functor (Exp env res a) where
  fmap = rmap

instance Profunctor (Exp e r) where
  dimap f g (Exp r) = Exp (dimap (lmap (lmap f)) (lmap (lmap (rmap g))) r)


-- Construction

exp :: (forall res . a -> (env ≁ b) • res -> res) -> Exp env res a b
exp f = Exp (\ ka -> (ka •) <<^ inK . flip f)

exp' :: (a -> b) -> Exp env res a b
exp' f = exp (\ a kb -> kb • pure (f a))


-- Elimination

runExp :: Exp env res a b -> b • res -> a -> env ==> res
runExp (Exp r) k a = C (\ env -> r (dn a) (k <<^ (env ∘)))
