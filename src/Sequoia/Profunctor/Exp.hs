module Sequoia.Profunctor.Exp
( -- * Exponential functors
  Exp(..)
  -- * Elimination
, appExp
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
  xf <*> xa = Exp (\ k a -> appExp xf a (appExp xa a . (k .)))


-- Elimination

appExp :: Exp r a b -> a -> (b -> r) -> r
appExp = flip . getExp

runExp :: (b -> r) -> a -> Exp r a b -> r
runExp k a x = getExp x k a
