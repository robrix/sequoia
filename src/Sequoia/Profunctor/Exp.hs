module Sequoia.Profunctor.Exp
( -- * Exponential functors
  Exp(..)
  -- * Elimination
, runExp
) where

import Data.Function ((&))
import Sequoia.Profunctor

-- Exponential functors

newtype Exp r a b = Exp { getExp :: (b -> r) -> (a -> r) }

instance Profunctor (Exp r) where
  dimap f g = Exp . dimap (<<^ g) (<<^ f) . getExp

instance Functor (Exp r a) where
  fmap = rmap

instance Applicative (Exp r a) where
  pure = Exp . (const .) . (&)
  xf <*> xa = Exp (\ k a -> runExp xf a (runExp xa a . (k .)))


-- Elimination

runExp :: Exp r a b -> a -> (b -> r) -> r
runExp = flip . getExp
