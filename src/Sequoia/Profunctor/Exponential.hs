{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.Exponential
( -- * Exponential profunctor
  CP(..)
  -- ** Mixfix notation
, type (--|)
, type (|->)
  -- ** Exponential profunctor abstraction
, _Exponential
, Exponential(..)
, _Coexponential
, Coexponential(..)
  -- ** Construction
, inCP'
  -- ** Elimination
, evalCP
, appCP
, appCP2
, runCP
, elimCP
, argCS_
, argCS
, contCS
, contCS_
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, (↑)
, (↓)
, dnE
, coerceCP
, liftRunCP
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
, inPrd
, producer
, joinl
, consumer
, inCns
  -- * Modular computations
, I(..)
, O(..)
, MCP(..)
, CoMCP(..)
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Sequoia.Confunctor
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Optic.Iso
import           Sequoia.Optic.Lens
import           Sequoia.Profunctor.Applicative
import           Sequoia.Profunctor.Coexponential
import           Sequoia.Profunctor.Context
import           Sequoia.Value as V

-- Exponential profunctor

newtype CP e r a b = CP { getCP :: V e a -> K r b -> C e r }

instance Exponential CP where
  inCP = CP
  exCP = getCP

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
  (>>=) = bindCP

instance Coapply (CP e r) where
  coliftA2 f a b = CP (\ v k -> env ((flip (exCP a) k <∘∘> flip (exCP b) k) (f <$> v)))

instance Env2 CP where
  env2 f = inCP (\ v k -> env (runCP v k . f))

instance Res2 CP where
  res2 = inCP . const . const . res
  liftRes2 f = liftRunCP (\ run -> liftRes (dimap (. run) run f))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Exponential profunctor abstraction

_Exponential :: (Exponential f, Exponential f') => Iso (f e r a b) (f' e' r' a' b') (V e a -> K r b -> C e r) (V e' a' -> K r' b' -> C e' r')
_Exponential = exCP <-> inCP

class (forall e r . Cat.Category (f e r), forall e r . Profunctor (f e r)) => Exponential f where
  inCP :: (V e a -> K r b -> C e r) -> f e r a b
  exCP :: f e r a b -> V e a -> K r b -> C e r


_Coexponential :: (Coexponential p, Coexponential p') => Iso (p e r a b) (p' e' r' a' b') (Coexp e r b a) (Coexp e' r' b' a')
_Coexponential = exCS <-> inCS

class (forall e r . Confunctor (f e r)) => Coexponential f where
  inCS :: Coexp e r b a -> f e r a b
  exCS :: f e r a b -> Coexp e r b a


-- Construction

inCP' :: Exponential f => (a -> b) -> a --|f e r|-> b
inCP' f = inCP (\ a b -> b •∘ (f <$> a))


-- Elimination

evalCP :: Exponential f => e --|f e r|-> r -> (e -> r)
evalCP f = runC (exCP f idV idK)

appCP :: Exponential f => a --|f e r|-> b -> V e (V e a -> K r **b)
appCP f = inV (\ e a -> inK (\ b -> runC (exCP f a b) e))

appCP2 :: Exponential f => a --|f e r|-> b --|f e r|-> c -> V e (V e a -> V e b -> K r **c)
appCP2 f = inV (\ e a b -> inK (\ c -> runC (exCP f a (inK (\ g -> runC (exCP g b c) e))) e))

runCP :: Exponential f => V e a -> K r b -> a --|f e r|-> b -> C e r
runCP v k f = exCP f v k

elimCP :: (Exponential f, Coexponential s) => a --|f e r|-> b -> s e r a b -> C e r
elimCP f = (exCP f <$> recall <*> forget) . exCS


argCS_ :: Coexponential s => Lens (s e r a b) (s e' r a' b) (V e a) (V e' a')
argCS_ = _Coexponential.recall_

argCS :: Coexponential s => s e r a b -> V e a
argCS = recall . exCS

contCS_ :: Coexponential s => Lens (s e r a b) (s e r' a b') (K r b) (K r' b')
contCS_ = _Coexponential.forget_

contCS :: Coexponential s => s e r a b -> K r b
contCS = forget . exCS


-- Computation

(↑) :: Exponential f => a --|f e r|-> b -> V e a -> f e r e|-> b
f ↑ a = f <<< producer a

infixl 7 ↑

(↓) :: Exponential f => K r b -> a --|f e r|-> b -> a --|f e r|-> r
k ↓ f = consumer k <<< f

infixl 8 ↓

dnE :: Exponential f => K r **(a --|f e r|-> b) -> a --|f e r|-> b
dnE k = inCP (\ a b -> cont (\ _K -> k •• _K (\ f -> exCP f a b)))

coerceCP :: (Exponential c, Exponential d) => c e r a b -> d e r a b
coerceCP = inCP . exCP


liftRunCP :: Exponential f => ((f e r a b -> C e r) -> C e r) -> f e r a b
liftRunCP f = inCP (fmap f . runCP)


dimapVK :: Exponential f => (V e a' -> V e a) -> (K r b' -> K r b) -> (a --|f e r|-> b -> a' --|f e r|-> b')
dimapVK f g = inCP . dimap f (lmap g) . exCP

lmapV :: Exponential f => (V e a' -> V e a) -> (a --|f e r|-> b -> a' --|f e r|-> b)
lmapV = (`dimapVK` id)

rmapK :: Exponential f => (K r b' -> K r b) -> (a --|f e r|-> b -> a --|f e r|-> b')
rmapK = (id `dimapVK`)


-- Defaults

dimapCP :: Exponential f => (a' -> a) -> (b -> b') -> a --|f e r|-> b -> a' --|f e r|-> b'
dimapCP f g = dimapVK (fmap f) (contramap g)

lmapCP :: Exponential f => (a' -> a) -> a --|f e r|-> b -> a' --|f e r|-> b
lmapCP = lmapV . fmap

rmapCP :: Exponential f => (b -> b') -> a --|f e r|-> b -> a --|f e r|-> b'
rmapCP = rmapK . contramap

firstCP  :: Exponential f => a --|f e r|-> b -> (a, c) --|f e r|-> (b, c)
firstCP  r = inCP (\ a b -> val (\ (a, c) -> exCP r (inV0 a) (contramap (,c) b)) a)

secondCP :: Exponential f => a --|f e r|-> b -> (c, a) --|f e r|-> (c, b)
secondCP r = inCP (\ a b -> val (\ (c, a) -> exCP r (inV0 a) (contramap (c,) b)) a)

leftCP  :: Exponential f => a --|f e r|-> b -> Either a c --|f e r|-> Either b c
leftCP  r = inCP (\ a b -> val (flip (exCP r) (inlK b) . inV0 <--> (inrK b ••)) a)

rightCP :: Exponential f => a --|f e r|-> b -> Either c a --|f e r|-> Either c b
rightCP r = inCP (\ a b -> val ((inlK b ••) <--> flip (exCP r) (inrK b) . inV0) a)

wanderCP :: (Exponential f, Applicative (f e r e)) => (forall m . Applicative m => (a -> m b) -> (s -> m t)) -> a --|f e r|-> b -> s --|f e r|-> t
wanderCP traverse r = inCP (\ s t -> val (\ s -> exCP (traverse ((r ↑) . inV0) s) idV t) s)

idCP :: Exponential f => a --|f e r|-> a
idCP = inCP (flip (•∘))

composeCP :: Exponential f => b --|f e r|-> c -> a --|f e r|-> b -> a --|f e r|-> c
composeCP f g = inCP (\ a c -> cont (\ _K -> exCP g a (_K (\ b -> exCP f (inV0 b) c))))

pureCP :: Exponential f => b -> a --|f e r|-> b
pureCP = inCP . const . flip (••)

apCP :: Exponential f => a --|f e r|-> (b -> c) -> a --|f e r|-> b -> a --|f e r|-> c
apCP df da = inCP (\ a b -> cont (\ _K -> exCP df a (_K (\ f -> exCP da a (contramap f b)))))

bindCP :: Exponential f => a --|f e r|-> b -> (b -> a --|f e r|-> c) -> a --|f e r|-> c
bindCP m f = inCP (\ a c -> cont (\ _K -> exCP m a (_K (\ b -> exCP (f b) a c))))


-- Control context

(•∘) :: (Env c, V.Representable v, Res c, K.Representable k) => k a -> v a -> c (V.Rep v) (K.Rep k)
k •∘ v = env (\ e -> res (k • e ∘ v))

infix 7 •∘

localEnv :: Exponential c => (e -> e') -> c e' r s t -> c e r s t
-- FIXME: this always evaluates the argument in the current scope
localEnv f c = inCP (\ v k -> val (\ v -> lmap f (exCP c (inV0 v) k)) v)


inPrd :: Exponential f => (K r a -> C e r) -> f e r e|-> a
inPrd = inCP . const

producer :: (Exponential f, V.Representable v, V.Rep v ~ e) => v a -> f e r e|-> a
producer v = inPrd (•∘ v)

joinl :: Exponential f => f e r e|-> f e r a b -> f e r a b
joinl p = inCP (\ a b -> cont (\ _K -> exCP p idV (_K (\ f -> exCP f a b))))


inCns :: Exponential f => (V e a -> C e r) -> a --|f e r|-> r
inCns = inCP . fmap const

consumer :: (Exponential f, K.Representable k, K.Rep k ~ r) => k a -> a --|f e r|-> r
consumer k = inCns (k •∘)


-- Modular computations

newtype I p a c e r = I { runI :: V e a `p` c e r }

instance (forall x . Functor (c x), forall x . Functor (p x)) => Functor (I p a c e) where
  fmap f = I . fmap (fmap f) . runI

instance (Env c, p ~ (->)) => Env (I p a c) where
  env f = I (\ v -> env ((`runI` v) . f))

instance (Res c, p ~ (->)) => Res (I p a c) where
  res r = I (const (res r))
  liftRes f = I (\ v -> let run = (`runI` v) in liftRes (run . f . (. run)))


newtype O p b c e r = O { runO :: K r b `p` c e r }

instance (Env c, p ~ (->)) => Env (O p a c) where
  env f = O (\ k -> env ((`runO` k) . f))

instance (Res c, p ~ (->)) => Res (O p a c) where
  res r = O (const (res r))
  liftRes f = O (\ k -> let run = (`runO` k) in liftRes (run . f . (. run)))


newtype MCP e r a b = MCP { runMCP :: I (->) a (O (->) b C) e r }

instance Env2 MCP where
  env2 f = MCP (env (runMCP . f))

newtype CoMCP e r a b = CoMCP { runCoMCP :: I (,) a (O (,) b C) e r }
