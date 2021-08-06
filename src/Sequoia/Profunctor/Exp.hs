module Sequoia.Profunctor.Exp
( -- * Exponential functors
  Exp(..)
  -- * Construction
, exp
  -- * Elimination
, appExp
, runExp
, elimExp
  -- * Coexponential functors
, Coexp(..)
  -- * Elimination
, elimCoexp
) where

import Data.Function ((&))
import Prelude hiding (exp)
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

instance Monad (Exp r a) where
  m >>= f = Exp (\ k a -> runExp (runExp k a . f) a m)


-- Construction

exp :: (a -> b) -> Exp r a b
exp = Exp . flip (.)


-- Elimination

appExp :: Exp r a b -> a -> (b -> r) -> r
appExp = flip . getExp

runExp :: (b -> r) -> a -> Exp r a b -> r
runExp k a x = getExp x k a

elimExp :: Exp r a b -> Coexp r b a -> r
elimExp f (b :>- a) = appExp f a b


-- Coexponential functors

data Coexp r b a = (b -> r) :>- a

infixr 0 :>-

instance Profunctor (Coexp r) where
  dimap f g (b :>- a) = (b <<^ f) :>- g a

instance Functor (Coexp r b) where
  fmap = rmap


-- Elimination

elimCoexp :: Coexp r a b -> Exp r b a -> r
elimCoexp (b :>- a) f = appExp f a b
