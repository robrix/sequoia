{-# LANGUAGE FunctionalDependencies #-}
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
  -- * Control context
, (•∘)
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
  dimap f g = CP . dimap (fmap f) (lmap (contramap g)) . getCP

instance Strong (CP e r) where
  first'  (CP r) = CP (\ a b -> val (\ (a, c) -> r (inV0 a) (contramap (,c) b)) a)
  second' (CP r) = CP (\ a b -> val (\ (c, a) -> r (inV0 a) (contramap (c,) b)) a)

instance Choice (CP e r) where
  left'  (CP r) = CP (\ a b -> val ((`r` inlK b) . inV0 <--> (inrK b ••)) a)
  right' (CP r) = CP (\ a b -> val ((inlK b ••) <--> (`r` inrK b) . inV0) a)

instance Traversing (CP e r) where
  wander traverse r = CP (\ s t -> val (\ s -> exCP (traverse ((r ↑) . inV0) s) idV t) s)

instance Cat.Category (CP e r) where
  id = CP (flip (•∘))
  CP f . CP g = CP (\ a c -> cont (\ _K -> g a (_K (\ b -> f (inV0 b) c))))

instance Functor (CP e r c) where
  fmap f = CP . fmap (lmap (contramap f)) . getCP

instance Applicative (CP e r a) where
  pure a = CP (\ _ b -> b •• a)

  CP df <*> CP da = CP (\ a b -> cont (\ _K -> df a (_K (\ f -> da a (contramap f b)))))

instance Monad (CP e r a) where
  CP m >>= f = CP (\ a c -> cont (\ _K -> m a (_K (\ b -> getCP (f b) a c))))

instance Coapply (CP e r) where
  coliftA2 f a b = CP (\ v k -> env ((flip (exCP a) k <∘∘> flip (exCP b) k) (f <$> v)))

instance Env e (CP e r a b) where
  env f = CP (\ v k -> env (runCP v k . f))

  type WithEnv (CP e r a b) e' = CP e' r a b

  -- FIXME: this could change the semantics of programs dependent on dynamic vs. lexical scoping.
  localEnv f c = CP (\ v k -> val (\ v -> localEnv f (getCP c (inV0 v) k)) v)

instance Res r (CP e r a b) where
  res = CP . const . const . res
  liftRes f = CP (\ v k -> liftRes (\ run -> exCP (f (run . runCP v k)) v k))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Control-passing profunctor abstraction

_ControlPassing :: ControlPassing e r f => f a b <-> (V e a -> K r b -> Control e r)
_ControlPassing = exCP <-> inCP

class (Cat.Category f, Profunctor f) => ControlPassing e r f | f -> e r where
  inCP :: (V e a -> K r b -> Control e r) -> f a b
  exCP :: f a b -> V e a -> K r b -> Control e r

instance ControlPassing e r (CP e r) where
  inCP = CP
  exCP = getCP


-- Construction

inCP' :: ControlPassing e r f => (a -> b) -> a --|f|-> b
inCP' f = inCP (\ a b -> b •∘ (f <$> a))


-- Elimination

evalCP :: ControlPassing e r f => e --|f|-> r -> (e -> r)
evalCP f = getControl (exCP f (inV id) idK)

appCP :: ControlPassing e r f => a --|f|-> b -> V e (V e a -> K r **b)
appCP f = inV (\ e a -> inK (\ b -> getControl (exCP f a b) e))

appCP2 :: ControlPassing e r f => a --|f|-> b --|f|-> c -> V e (V e a -> V e b -> K r **c)
appCP2 f = inV (\ e a b -> inK (\ c -> getControl (exCP f a (inK (\ g -> getControl (exCP g b c) e))) e))

runCP :: ControlPassing e r f => V e a -> K r b -> a --|f|-> b -> Control e r
runCP v k f = exCP f v k


-- Computation

(↑) :: ControlPassing e r f => a --|f|-> b -> V e a -> f e|-> b
f ↑ a = f <<< producer a

infixl 7 ↑

(↓) :: ControlPassing e r f => K r b -> a --|f|-> b -> a --|f|-> r
k ↓ f = consumer k <<< f

infixl 8 ↓

dnE :: ControlPassing e r f => K r **(a --|f|-> b) -> a --|f|-> b
dnE k = inCP (\ a b -> cont (\ _K -> k •• _K (\ f -> exCP f a b)))

coerceCP :: (ControlPassing k v c, ControlPassing k v d) => c a b -> d a b
coerceCP = inCP . exCP


-- Control context

(•∘) :: (Env (V.Rep v) c, V.Representable v, Res (K.Rep k) c, K.Representable k) => k a -> v a -> c
k •∘ v = env (\ e -> res (k • e ∘ v))

infix 7 •∘


newtype Control e r = Control { getControl :: e -> r }
  deriving (Cat.Category, Profunctor)

instance Env e (Control e r) where
  env f = Control (getControl =<< f)

  type WithEnv (Control e r) e' = Control e' r

  localEnv f = Control . lmap f . getControl

instance Res r (Control e r) where
  res = Control . const
  liftRes f = Control (\ e -> let run = (`getControl` e) in run (f run))


inPrd :: ControlPassing e r f => (K r a -> Control e r) -> f e a
inPrd = inCP . const

producer :: (ControlPassing e r f, V.Representable v, V.Rep v ~ e) => v a -> f e a
producer v = inPrd (•∘ v)

joinl :: ControlPassing e r f => f e (f a b) -> f a b
joinl p = inCP (\ a b -> cont (\ _K -> exCP p idV (_K (\ f -> exCP f a b))))


inCns :: ControlPassing e r f => (V e a -> Control e r) -> f a r
inCns = inCP . fmap const

consumer :: (ControlPassing e r f, K.Representable k, K.Rep k ~ r) => k a -> f a r
consumer k = inCns (k •∘)
