{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.D
( -- * Dual profunctor
  D(..)
  -- ** Mixfix notation
, type (--|)
, type (|->)
  -- ** Dual profunctor abstraction
, _D
, Dual(..)
  -- ** Construction
, inD'
, inDK
, inDV
  -- ** Elimination
, exDK
, exDV
, evalD
, appD
, appD2
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, (↑)
, (<↑)
, (↓)
, (↓>)
, dnE
, coerceD
  -- * Control context
, Control(..)
, ControlT(..)
, Context(..)
, withEnv
, withVal
, liftRunControlWith
, liftKWith
, (•∘)
, (••)
, complete
, runComplete
, Complete
, inPrd
, producer
, joinl
, Producer
, consumer
, inCns
, Consumer
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Control.Monad.Trans.Class
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Sequoia.Bijection
import           Sequoia.Conjunction
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Profunctor.Applicative
import           Sequoia.Value as V

-- Dual profunctor

newtype D r e a b = D { runD :: V e a -> K r b -> Context r e }

instance Profunctor (D r e) where
  dimap f g = D . dimap (fmap f) (lmap (contramap g)) . runD

instance Strong (D r e) where
  first'  (D r) = D (\ a b -> withVal (\ (a, c) -> r (inV0 a) (contramap (,c) b)) a)
  second' (D r) = D (\ a b -> withVal (\ (c, a) -> r (inV0 a) (contramap (c,) b)) a)

instance Choice (D r e) where
  left'  (D r) = D (\ a b -> withVal ((`r` inlK b) . inV0 <--> (inrK b ••)) a)
  right' (D r) = D (\ a b -> withVal ((inlK b ••) <--> (`r` inrK b) . inV0) a)

instance Traversing (D r e) where
  wander traverse r = D (\ s t -> withVal (\ s -> exD (traverse ((r ↑) . inV0) s) idV t) s)

instance Cat.Category (D r e) where
  id = D (flip (•∘))
  D f . D g = D (\ a c -> liftKWith (\ _K -> g a (_K (\ b -> f (inV0 b) c))))

instance Functor (D r e c) where
  fmap f = D . fmap (lmap (contramap f)) . runD

instance Applicative (D r e a) where
  pure a = D (\ _ b -> b •• a)

  D df <*> D da = D (\ a b -> liftKWith (\ _K -> df a (_K (\ f -> da a (contramap f b)))))

instance Monad (D r e a) where
  D m >>= f = D (\ a c -> liftKWith (\ _K -> m a (_K (\ b -> runD (f b) a c))))

instance Coapply (D r e) where
  coliftA2 f a b = D (\ v k -> withEnv ((flip (exD a) k <∘∘> flip (exD b) k) (f <$> v)))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Dual profunctor abstraction

_D :: Dual r e d => d a b <-> (V e a -> K r b -> Context r e)
_D = exD <-> inD

class (Cat.Category d, Profunctor d, R d ~ r, E d ~ e) => Dual r e d | d -> r e where
  inD :: (V e a -> K r b -> Context r e) -> d a b
  exD :: d a b -> V e a -> K r b -> Context r e

  type R d
  type E d

instance Dual r e (D r e) where
  inD = D
  exD = runD

  type R (D r e) = r
  type E (D r e) = e


-- Construction

inD' :: Dual r e d => (a -> b) -> a --|d|-> b
inD' f = inD (\ a b -> b •∘ (f <$> a))

inDK :: Dual r e d => (K r b -> K r a) -> a --|d|-> b
inDK f = inD (\ a b -> f b •∘ a)

inDV :: Dual r e d => (V e a -> V e b) -> a --|d|-> b
inDV f = inD (\ a b -> b •∘ f a)


-- Elimination

exDK :: Dual r e d => a --|d|-> b -> V e (K r b -> K r a)
exDK f = inV (\ e k -> inK (\ a -> runContext (exD f (inV0 a) k) e))

exDV :: Dual r e d => K r' (V e a -> V e r) -> K r' (a --|d|-> r)
exDV k = inK (\ f -> k • inV . \ a -> runContext (exD f a idK))

evalD :: Dual r e d => e --|d|-> r -> (e -> r)
evalD f = runContext (exD f (inV id) idK)

appD :: Dual r e d => a --|d|-> b -> V e (V e a -> K r **b)
appD f = inV (\ e a -> inK (\ b -> runControl (exD f a b) e))

appD2 :: Dual r e d => a --|d|-> b --|d|-> c -> V e (V e a -> V e b -> K r **c)
appD2 f = inV (\ e a b -> inK (\ c -> runControl (exD f a (inK (\ g -> runControl (exD g b c) e))) e))


-- Computation

(↑) :: Dual r e d => a --|d|-> b -> V e a -> Producer d s b
f ↑ a = f <<< producer a

infixl 7 ↑

(<↑) :: Dual r e d => Conj c => (a `c` _Γ) --|d|-> _Δ -> a -> _Γ --|d|-> _Δ
f <↑ a = f <<< inD' (inlr a)

infixl 7 <↑

(↓) :: Dual r e d => K r b -> a --|d|-> b -> Consumer d r a
k ↓ f = consumer k <<< f

infixl 8 ↓

(↓>) :: (Dual r e d, Disj p) => K r c -> a --|d|-> (b `p` c) -> a --|d|-> b
c ↓> f = inD (\ v k -> (k <••> c) •∘ v) <<< f

infixr 9 ↓>

dnE :: Dual r e d => K r **(a --|d|-> b) -> a --|d|-> b
dnE k = inD (\ a b -> liftKWith (\ _K -> k •• _K (\ f -> exD f a b)))

coerceD :: (Dual k v c, Dual k v d) => c a b -> d a b
coerceD = inD . exD


-- Control context

class Control r e c | c -> r e where
  control :: (e -> r) -> c
  runControl :: c -> (e -> r)


newtype ControlT r e m a = ControlT { runControlT :: e -> (a -> m r) -> m r }
  deriving (Functor)

instance Applicative (ControlT r e m) where
  pure a = ControlT $ \ _ k -> k a
  ControlT f <*> ControlT a = ControlT (\ e k -> f e (a e . (k .)))

instance Monad (ControlT r e m) where
  ControlT a >>= f = ControlT (\ e k -> a e (\ a' -> runControlT (f a') e k))

instance MonadTrans (ControlT r e) where
  lift m = ControlT (const (m >>=))


newtype Context r e = Context { runContext :: e -> r }

instance Control r e (Context r e) where
  control = Context
  runControl = runContext

instance Applicative m => Control (m r) e (ControlT r e m r) where
  control f = ControlT (\ e _ -> f e)
  runControl c e = runControlT c e pure

instance Control r e (D r e e r) where
  control = complete . Context
  runControl = runContext . runComplete


withEnv :: Control r e c => (e -> c) -> c
withEnv f = control (runControl =<< f)

withVal :: Control r e c => (a -> c) -> (V e a -> c)
withVal f v = withEnv (f . exV v)

liftRunControlWith :: Control r e c => ((c -> r) -> c) -> c
liftRunControlWith f = withEnv (f . flip runControl)

liftKWith :: Control r e c => (((a -> c) -> K r a) -> c) -> c
liftKWith f = liftRunControlWith (\ run -> f (inK . (run .)))

(•∘) :: Control r e c => K r a -> V e a -> c
k •∘ v = control (\ e -> k • e ∘ v)

infix 7 •∘

(••) :: Control r e c => K r a -> a -> c
k •• v = control (const (k • v))

infix 7 ••


complete :: (Dual r e d, Control r e c) => c -> Complete d r e
complete = inD . const . const . control . runControl

runComplete :: (Dual r e d, Control r e c) => Complete d r e -> c
runComplete f = control (runControl (exD f idV idK))

type Complete d r e = d e r


inPrd :: Dual r e d => (K r a -> Context r e) -> Producer d s a
inPrd = inD . const

producer :: Dual r e d => V e a -> Producer d s a
producer v = inPrd (•∘ v)

joinl :: Dual r e d => Producer d e (d a b) -> d a b
joinl p = inD (\ a b -> liftKWith (\ _K -> exD p idV (_K (\ f -> exD f a b))))

type Producer d s b = d s b


inCns :: Dual r e d => (V e a -> Context r e) -> Consumer d r a
inCns = inD . fmap const

consumer :: Dual r e d => K r a -> Consumer d r a
consumer k = inCns (k •∘)

type Consumer d r a = d a r
