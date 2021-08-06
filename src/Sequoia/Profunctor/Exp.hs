module Sequoia.Profunctor.Exp
( -- * Exponential functors
  Exp(..)
  -- * Mixfix syntax
, type (~~)
, type (~>)
  -- * Construction
, exp
  -- * Elimination
, appExp
, runExp
, elimExp
, (#)
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
import           Data.Function ((&))
import           Prelude hiding (exp)
import           Sequoia.Disjunction
import           Sequoia.Profunctor

-- Exponential functors

newtype Exp r a b = Exp { getExp :: (b -> r) -> (a -> r) }

instance Cat.Category (Exp r) where
  id = exp id
  f . g = Exp (getExp g . getExp f)

instance Profunctor (Exp r) where
  dimap f g = Exp . dimap (<<^ g) (<<^ f) . getExp

instance Choice (Exp r) where
  left'  (Exp r) = Exp (\ k -> r (inlL k) <--> inrL k)
  right' (Exp r) = Exp (\ k -> inlL k <--> r (inrL k))

instance Cochoice (Exp r) where
  unleft  (Exp f) = Exp (\ k -> inlL (let f' = f (k <--> inrL f') in f'))
  unright (Exp f) = Exp (\ k -> inrL (let f' = f (inlL f' <--> k) in f'))

instance Strong (Exp r) where
  first'  f = Exp (\ k (a, c) -> appExp f a (k . (,c)))
  second' f = Exp (\ k (c, a) -> appExp f a (k . (c,)))

instance Functor (Exp r a) where
  fmap = rmap

instance Applicative (Exp r a) where
  pure = Exp . (const .) . (&)
  xf <*> xa = Exp (\ k a -> appExp xf a (appExp xa a . (k .)))

instance Monad (Exp r a) where
  m >>= f = Exp (\ k a -> runExp (runExp k a . f) a m)


-- Mixfix syntax

type a ~~r = Exp r a
type r~> b = r b

infixr 1 ~~
infixr 0 ~>


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

(#) :: (a ~~b~> b) -> (a -> b)
f # a = appExp f a id

infixl 9 #


-- Computation



-- Coexponential functors

data Coexp r b a = (b -> r) :>- a

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

(>-) :: (b -> r) -> a -> Coexp r b a
(>-) = (:>-)


-- Elimination

runCoexp :: (a -> b) -> Coexp r b a -> r
runCoexp f (b :>- a) = b (f a)

elimCoexp :: Coexp r a b -> Exp r b a -> r
elimCoexp (a :>- b) (Exp f) = f a b

withCoexp :: Coexp r a b -> ((a -> r) -> b -> s) -> s
withCoexp (a :>- b) f = f a b


-- Computation

cocurry :: Exp r c (Either a b) -> Exp r (Coexp r b c) a
cocurry f = Exp (\ k (b :>- c) -> appExp f c (either k b))

uncocurry :: Exp r (Coexp r b c) a -> Exp r c (Either a b)
uncocurry f = Exp (\ k c -> appExp f (inrL k >- c) (inlL k))

coap :: Exp r c (Either (Coexp r b c) b)
coap = Exp (\ k -> inlL k . (inrL k >-))
