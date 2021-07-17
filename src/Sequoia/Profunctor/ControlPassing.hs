{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.ControlPassing
( -- * Control-passing profunctor
  CP(..)
  -- ** Mixfix notation
, type (--|)
, type (|->)
  -- ** Control-passing profunctor abstraction
, _ControlPassing
, ControlPassing(..)
  -- ** Construction
, inCP'
  -- ** Elimination
, evalCP
, appCP
, appCP2
, runCP
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, (↑)
, (↓)
, dnE
, coerceCP
, dimapVK
, lmapV
, rmapK
  -- * Defaults
, dimapCP
, lmapCP
, rmapCP
, firstCP
, secondCP
, leftCP
, rightCP
, wanderCP
, idCP
, composeCP
, pureCP
, apCP
, bindCP
  -- * Control context
, (•∘)
, localEnv
, Control(..)
, inPrd
, producer
, joinl
, consumer
, inCns
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Sequoia.Bijection
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Profunctor.Applicative
import           Sequoia.Value as V

-- Control-passing profunctor

newtype CP e r a b = CP { getCP :: V e a -> K r b -> Control e r }

instance Profunctor (CP e r) where
  dimap = dimapCP

instance Strong (CP e r) where
  first'  = firstCP
  second' = secondCP

instance Choice (CP e r) where
  left'  = leftCP
  right' = rightCP

instance Traversing (CP e r) where
  wander = wanderCP

instance Cat.Category (CP e r) where
  id = idCP
  (.) = composeCP

instance Functor (CP e r c) where
  fmap = rmap

instance Applicative (CP e r a) where
  pure = pureCP
  (<*>) = apCP

instance Monad (CP e r a) where
  CP m >>= f = CP (\ a c -> cont (\ _K -> m a (_K (\ b -> getCP (f b) a c))))

instance Coapply (CP e r) where
  coliftA2 f a b = CP (\ v k -> env ((flip (exCP a) k <∘∘> flip (exCP b) k) (f <$> v)))

instance Env e (CP e r a b) where
  env f = CP (\ v k -> env (runCP v k . f))

instance Res r (CP e r a b) where
  res = CP . const . const . res
  liftRes f = CP (\ v k -> liftRes (\ run -> exCP (f (run . runCP v k)) v k))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Control-passing profunctor abstraction

_ControlPassing :: ControlPassing f => f e r a b <-> (V e a -> K r b -> Control e r)
_ControlPassing = exCP <-> inCP

class (forall e r . Cat.Category (f e r), forall e r . Profunctor (f e r)) => ControlPassing f where
  inCP :: (V e a -> K r b -> Control e r) -> f e r a b
  exCP :: f e r a b -> V e a -> K r b -> Control e r

instance ControlPassing CP where
  inCP = CP
  exCP = getCP


-- Construction

inCP' :: ControlPassing f => (a -> b) -> a --|f e r|-> b
inCP' f = inCP (\ a b -> b •∘ (f <$> a))


-- Elimination

evalCP :: ControlPassing f => e --|f e r|-> r -> (e -> r)
evalCP f = getControl (exCP f (inV id) idK)

appCP :: ControlPassing f => a --|f e r|-> b -> V e (V e a -> K r **b)
appCP f = inV (\ e a -> inK (\ b -> getControl (exCP f a b) e))

appCP2 :: ControlPassing f => a --|f e r|-> b --|f e r|-> c -> V e (V e a -> V e b -> K r **c)
appCP2 f = inV (\ e a b -> inK (\ c -> getControl (exCP f a (inK (\ g -> getControl (exCP g b c) e))) e))

runCP :: ControlPassing f => V e a -> K r b -> a --|f e r|-> b -> Control e r
runCP v k f = exCP f v k


-- Computation

(↑) :: ControlPassing f => a --|f e r|-> b -> V e a -> f e r e|-> b
f ↑ a = f <<< producer a

infixl 7 ↑

(↓) :: ControlPassing f => K r b -> a --|f e r|-> b -> a --|f e r|-> r
k ↓ f = consumer k <<< f

infixl 8 ↓

dnE :: ControlPassing f => K r **(a --|f e r|-> b) -> a --|f e r|-> b
dnE k = inCP (\ a b -> cont (\ _K -> k •• _K (\ f -> exCP f a b)))

coerceCP :: (ControlPassing c, ControlPassing d) => c e r a b -> d e r a b
coerceCP = inCP . exCP


dimapVK :: ControlPassing f => (V e a' -> V e a) -> (K r b' -> K r b) -> (a --|f e r|-> b -> a' --|f e r|-> b')
dimapVK f g = inCP . dimap f (lmap g) . exCP

lmapV :: ControlPassing f => (V e a' -> V e a) -> (a --|f e r|-> b -> a' --|f e r|-> b)
lmapV = (`dimapVK` id)

rmapK :: ControlPassing f => (K r b' -> K r b) -> (a --|f e r|-> b -> a --|f e r|-> b')
rmapK = (id `dimapVK`)


-- Defaults

dimapCP :: ControlPassing f => (a' -> a) -> (b -> b') -> a --|f e r|-> b -> a' --|f e r|-> b'
dimapCP f g = dimapVK (fmap f) (contramap g)

lmapCP :: ControlPassing f => (a' -> a) -> a --|f e r|-> b -> a' --|f e r|-> b
lmapCP = lmapV . fmap

rmapCP :: ControlPassing f => (b -> b') -> a --|f e r|-> b -> a --|f e r|-> b'
rmapCP = rmapK . contramap

firstCP  :: ControlPassing f => a --|f e r|-> b -> (a, c) --|f e r|-> (b, c)
firstCP  r = inCP (\ a b -> val (\ (a, c) -> exCP r (inV0 a) (contramap (,c) b)) a)

secondCP :: ControlPassing f => a --|f e r|-> b -> (c, a) --|f e r|-> (c, b)
secondCP r = inCP (\ a b -> val (\ (c, a) -> exCP r (inV0 a) (contramap (c,) b)) a)

leftCP  :: ControlPassing f => a --|f e r|-> b -> Either a c --|f e r|-> Either b c
leftCP  r = inCP (\ a b -> val (flip (exCP r) (inlK b) . inV0 <--> (inrK b ••)) a)

rightCP :: ControlPassing f => a --|f e r|-> b -> Either c a --|f e r|-> Either c b
rightCP r = inCP (\ a b -> val ((inlK b ••) <--> flip (exCP r) (inrK b) . inV0) a)

wanderCP :: (ControlPassing f, Applicative (f e r e)) => (forall m . Applicative m => (a -> m b) -> (s -> m t)) -> a --|f e r|-> b -> s --|f e r|-> t
wanderCP traverse r = inCP (\ s t -> val (\ s -> exCP (traverse ((r ↑) . inV0) s) idV t) s)

idCP :: ControlPassing f => a --|f e r|-> a
idCP = inCP (flip (•∘))

composeCP :: ControlPassing f => b --|f e r|-> c -> a --|f e r|-> b -> a --|f e r|-> c
composeCP f g = inCP (\ a c -> cont (\ _K -> exCP g a (_K (\ b -> exCP f (inV0 b) c))))

pureCP :: ControlPassing f => b -> a --|f e r|-> b
pureCP = inCP . const . flip (••)

apCP :: ControlPassing f => a --|f e r|-> (b -> c) -> a --|f e r|-> b -> a --|f e r|-> c
apCP df da = inCP (\ a b -> cont (\ _K -> exCP df a (_K (\ f -> exCP da a (contramap f b)))))

bindCP :: ControlPassing f => a --|f e r|-> b -> (b -> a --|f e r|-> c) -> a --|f e r|-> c
bindCP m f = inCP (\ a c -> cont (\ _K -> exCP m a (_K (\ b -> exCP (f b) a c))))


-- Control context

(•∘) :: (Env (V.Rep v) c, V.Representable v, Res (K.Rep k) c, K.Representable k) => k a -> v a -> c
k •∘ v = env (\ e -> res (k • e ∘ v))

infix 7 •∘

localEnv :: ControlPassing c => (e -> e') -> c e' r s t -> c e r s t
-- FIXME: this always evaluates the argument in the current scope
localEnv f c = inCP (\ v k -> val (\ v -> lmap f (exCP c (inV0 v) k)) v)


newtype Control e r = Control { getControl :: e -> r }
  deriving (Cat.Category, Profunctor)

instance Env e (Control e r) where
  env f = Control (getControl =<< f)

instance Res r (Control e r) where
  res = Control . const
  liftRes f = Control (\ e -> let run = (`getControl` e) in run (f run))


inPrd :: ControlPassing f => (K r a -> Control e r) -> f e r e a
inPrd = inCP . const

producer :: (ControlPassing f, V.Representable v, V.Rep v ~ e) => v a -> f e r e a
producer v = inPrd (•∘ v)

joinl :: ControlPassing f => f e r e (f e r a b) -> f e r a b
joinl p = inCP (\ a b -> cont (\ _K -> exCP p idV (_K (\ f -> exCP f a b))))


inCns :: ControlPassing f => (V e a -> Control e r) -> f e r a r
inCns = inCP . fmap const

consumer :: (ControlPassing f, K.Representable k, K.Rep k ~ r) => k a -> f e r a r
consumer k = inCns (k •∘)
