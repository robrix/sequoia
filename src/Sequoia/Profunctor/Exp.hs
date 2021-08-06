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
  -- * Construction
, (>-)
  -- * Elimination
, elimCoexp
) where

import Data.Function ((&))
import Prelude hiding (exp)
import Sequoia.Profunctor
import Sequoia.Profunctor.Applicative

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

instance Coapply (Coexp r) (Exp r) where
  coliftC2 f (Exp a) (Exp b) = Exp (\ k c -> a k (f (b k :>- c)))
  Exp f <&> Exp a = Exp (\ k b -> f k (a k :>- b))

instance Coapplicative (Coexp r) (Exp r) where
  copure f = Exp (\ _ (a :>- b) -> a (f b))


-- Construction

exp :: (a -> b) -> Exp r a b
exp = Exp . flip (.)


-- Elimination

appExp :: Exp r a b -> a -> (b -> r) -> r
appExp = flip . getExp

runExp :: (b -> r) -> a -> Exp r a b -> r
runExp k a x = getExp x k a

elimExp :: Exp r a b -> Coexp r b a -> r
elimExp (Exp f) (b :>- a) = f b a


-- Coexponential functors

data Coexp r b a = (b -> r) :>- a

infixr 0 :>-

instance Profunctor (Coexp r) where
  dimap f g (b :>- a) = (b <<^ f) :>- g a

instance Functor (Coexp r b) where
  fmap = rmap


-- Construction

(>-) :: (b -> r) -> a -> Coexp r b a
(>-) = (:>-)


-- Elimination

elimCoexp :: Coexp r a b -> Exp r b a -> r
elimCoexp (a :>- b) (Exp f) = f a b
