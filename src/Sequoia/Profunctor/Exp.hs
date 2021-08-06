module Sequoia.Profunctor.Exp
( -- * Exponential functors
  Exp(..)
  -- * Mixfix syntax
, type (~~)
, type (~>)
  -- * Construction
, exp
, exp'
, expFn
  -- * Elimination
, appExp
, runExp
, elimExp
, (#)
, getExpFn
  -- * Coexponential functors
, Coexp(..)
  -- * Mixfix syntax
, type (>-)
, type (-~)
  -- * Construction
, (>-)
  -- * Elimination
, runCoexp
, elimCoexp
, withCoexp
  -- * Computation
, cocurry
, uncocurry
, coap
) where

import qualified Control.Category as Cat
import           Data.Coerce
import           Prelude hiding (exp)
import           Sequoia.Disjunction
import           Sequoia.Monad.Run
import           Sequoia.Profunctor
import           Sequoia.Profunctor.Continuation

-- Exponential functors

newtype Exp r a b = Exp { getExp :: (b • r) -> (a • r) }

instance Cat.Category (Exp r) where
  id = exp' id
  f . g = Exp (getExp g . getExp f)

instance Profunctor (Exp r) where
  dimap f g = Exp . dimap (<<^ g) (<<^ f) . getExp

instance Choice (Exp r) where
  left'  f = Exp (\ k -> getExp f (inlL k) <••> inrL k)
  right' f = Exp (\ k -> inlL k <••> getExp f (inrL k))

instance Cochoice (Exp r) where
  unleft  f = Exp (\ k -> inlL (let f' = getExp f (k <••> inrL f') in f'))
  unright f = Exp (\ k -> inrL (let f' = getExp f (inlL f' <••> k) in f'))

instance Strong (Exp r) where
  first'  f = Exp (\ k -> K (\ (a, c) -> getExp f (lmap (,c) k) • a))
  second' f = Exp (\ k -> K (\ (c, a) -> getExp f (lmap (c,) k) • a))

instance Functor (Exp r a) where
  fmap = rmap

instance Applicative (Exp r a) where
  pure = Exp . fmap (K . const) . flip (•)
  xf <*> xa = Exp (\ k -> cont (\ _K -> getExp xf (_K (getExp xa . (k <<^)))))

instance Monad (Exp r a) where
  m >>= f = Exp (\ k -> K (\ a -> runExp (runExp k a <<^ f) a • m))


-- Mixfix syntax

type a ~~r = Exp r a
type r~> b = r b

infixr 1 ~~
infixr 0 ~>


-- Construction

exp :: (b • r -> a • r) -> Exp r a b
exp = coerce

exp' :: (a -> b) -> Exp r a b
exp' = Exp . lmap

expFn :: ((b -> r) -> (a -> r)) -> Exp r a b
expFn = coerce


-- Elimination

appExp :: Exp r a b -> a -> b •• r
appExp f a = K ((• a) . getExp f)

runExp :: (b • r) -> a -> Exp r a b • r
runExp k a = K (\ f -> getExp f k • a)

elimExp :: Exp r a b -> Coexp r b a • r
elimExp f = K (\ (b :>- a) -> getExp f b • a)

(#) :: (a ~~b~> b) -> (a -> b)
f # a = appExp f a • idK

infixl 9 #

getExpFn :: Exp r a b -> ((b -> r) -> (a -> r))
getExpFn = coerce


-- Coexponential functors

data Coexp r b a = (b • r) :>- a

infixr 0 :>-

instance Profunctor (Coexp r) where
  dimap f g (b :>- a) = (b <<^ f) :>- g a

instance Functor (Coexp r b) where
  fmap = rmap


-- Mixfix syntax

type b >-r = Coexp r b
type r-~ a = r a

infixr 1 >-
infixr 0 -~


-- Construction

(>-) :: (b • r) -> a -> Coexp r b a
(>-) = (:>-)


-- Elimination

runCoexp :: (a -> b) -> Coexp r b a • r
runCoexp f = K (\ (b :>- a) -> b • f a)

elimCoexp :: Coexp r a b -> Exp r b a • r
elimCoexp (a :>- b) = K (\ (Exp f) -> f a • b)

withCoexp :: Coexp r a b -> ((a • r) -> b -> s) -> s
withCoexp (a :>- b) f = f a b


-- Computation

cocurry :: Exp r c (Either a b) -> Exp r (Coexp r b c) a
cocurry f = Exp (\ k -> K (\ (b :>- c) -> getExp f (k <••> b) • c))

uncocurry :: Exp r (Coexp r b c) a -> Exp r c (Either a b)
uncocurry f = Exp (\ k -> K (\ c -> getExp f (inlL k) • (inrL k >- c)))

coap :: Exp r c (Either (Coexp r b c) b)
coap = Exp (\ k -> lmap (inrL k >-) (inlL k))
