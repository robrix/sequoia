{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.ControlPassing
( -- * Control-passing profunctor
  CP(..)
  -- ** Mixfix notation
, type (--|)
, type (|->)
  -- ** Control-passing profunctor abstraction
, _D
, ControlPassing(..)
  -- ** Construction
, inD'
  -- ** Elimination
, evalD
, appD
, appD2
, runD
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, (↑)
, (↓)
, dnE
, coerceD
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
  wander traverse r = CP (\ s t -> val (\ s -> exD (traverse ((r ↑) . inV0) s) idV t) s)

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
  coliftA2 f a b = CP (\ v k -> env ((flip (exD a) k <∘∘> flip (exD b) k) (f <$> v)))

instance Env e (CP e r a b) where
  env f = CP (\ v k -> env (runD v k . f))

instance Res r (CP e r a b) where
  res = CP . const . const . res
  liftRes f = CP (\ v k -> liftRes (\ run -> exD (f (run . runD v k)) v k))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Control-passing profunctor abstraction

_D :: ControlPassing e r d => d a b <-> (V e a -> K r b -> Control e r)
_D = exD <-> inD

class (Cat.Category d, Profunctor d) => ControlPassing e r d | d -> e r where
  inD :: (V e a -> K r b -> Control e r) -> d a b
  exD :: d a b -> V e a -> K r b -> Control e r

instance ControlPassing e r (CP e r) where
  inD = CP
  exD = getCP


-- Construction

inD' :: ControlPassing e r d => (a -> b) -> a --|d|-> b
inD' f = inD (\ a b -> b •∘ (f <$> a))


-- Elimination

evalD :: ControlPassing e r d => e --|d|-> r -> (e -> r)
evalD f = getControl (exD f (inV id) idK)

appD :: ControlPassing e r d => a --|d|-> b -> V e (V e a -> K r **b)
appD f = inV (\ e a -> inK (\ b -> getControl (exD f a b) e))

appD2 :: ControlPassing e r d => a --|d|-> b --|d|-> c -> V e (V e a -> V e b -> K r **c)
appD2 f = inV (\ e a b -> inK (\ c -> getControl (exD f a (inK (\ g -> getControl (exD g b c) e))) e))

runD :: ControlPassing e r d => V e a -> K r b -> a --|d|-> b -> Control e r
runD v k f = exD f v k


-- Computation

(↑) :: ControlPassing e r d => a --|d|-> b -> V e a -> d e|-> b
f ↑ a = f <<< producer a

infixl 7 ↑

(↓) :: ControlPassing e r d => K r b -> a --|d|-> b -> a --|d|-> r
k ↓ f = consumer k <<< f

infixl 8 ↓

dnE :: ControlPassing e r d => K r **(a --|d|-> b) -> a --|d|-> b
dnE k = inD (\ a b -> cont (\ _K -> k •• _K (\ f -> exD f a b)))

coerceD :: (ControlPassing k v c, ControlPassing k v d) => c a b -> d a b
coerceD = inD . exD


-- Control context

(•∘) :: (Env (V.Rep v) c, V.Representable v, Res (K.Rep k) c, K.Representable k) => k a -> v a -> c
k •∘ v = env (\ e -> res (k • e ∘ v))

infix 7 •∘


newtype Control e r = Control { getControl :: e -> r }

instance Env e (Control e r) where
  env f = Control (getControl =<< f)

instance Res r (Control e r) where
  res = Control . const
  liftRes f = Control (\ e -> let run = (`getControl` e) in run (f run))


inPrd :: ControlPassing e r d => (K r a -> Control e r) -> d e a
inPrd = inD . const

producer :: (ControlPassing e r d, V.Representable v, V.Rep v ~ e) => v a -> d e a
producer v = inPrd (•∘ v)

joinl :: ControlPassing e r d => d e (d a b) -> d a b
joinl p = inD (\ a b -> cont (\ _K -> exD p idV (_K (\ f -> exD f a b))))


inCns :: ControlPassing e r d => (V e a -> Control e r) -> d a r
inCns = inD . fmap const

consumer :: (ControlPassing e r d, K.Representable k, K.Rep k ~ r) => k a -> d a r
consumer k = inCns (k •∘)
