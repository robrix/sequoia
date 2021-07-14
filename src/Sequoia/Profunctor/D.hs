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

newtype D r s a b = D { runD :: V s a -> K r b -> Context r s }

instance Profunctor (D r s) where
  dimap f g = D . dimap (fmap f) (lmap (contramap g)) . runD

instance Strong (D r s) where
  first'  (D r) = D (\ a b -> withVal (\ (a, c) -> r (inV0 a) (contramap (,c) b)) a)
  second' (D r) = D (\ a b -> withVal (\ (c, a) -> r (inV0 a) (contramap (c,) b)) a)

instance Choice (D r s) where
  left'  (D r) = D (\ a b -> withVal ((`r` inlK b) . inV0 <--> (inrK b ••)) a)
  right' (D r) = D (\ a b -> withVal ((inlK b ••) <--> (`r` inrK b) . inV0) a)

instance Traversing (D r s) where
  wander traverse r = D (\ s t -> withVal (\ s -> exD (traverse ((r ↑) . inV0) s) idV t) s)

instance Cat.Category (D r s) where
  id = D (flip (•∘))
  D f . D g = D (\ a c -> liftKWith (\ _K -> g a (_K (\ b -> f (inV0 b) c))))

instance Functor (D r s c) where
  fmap f = D . fmap (lmap (contramap f)) . runD

instance Applicative (D r s a) where
  pure a = D (\ _ b -> b •• a)

  D df <*> D da = D (\ a b -> liftKWith (\ _K -> df a (_K (\ f -> da a (contramap f b)))))

instance Monad (D r s a) where
  D m >>= f = D (\ a c -> liftKWith (\ _K -> m a (_K (\ b -> runD (f b) a c))))

instance Coapply (D r s) where
  coliftA2 f a b = D (\ v k -> withEnv ((flip (exD a) k <∘∘> flip (exD b) k) (f <$> v)))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Dual profunctor abstraction

_D :: Dual r s d => d a b <-> (V s a -> K r b -> Context r s)
_D = exD <-> inD

class (Cat.Category d, Profunctor d, R d ~ r, S d ~ s) => Dual r s d | d -> r s where
  inD :: (V s a -> K r b -> Context r s) -> d a b
  exD :: d a b -> V s a -> K r b -> Context r s

  type R d
  type S d

instance Dual r s (D r s) where
  inD = D
  exD = runD

  type R (D r s) = r
  type S (D r s) = s


-- Construction

inD' :: Dual r s d => (a -> b) -> a --|d|-> b
inD' f = inD (\ a b -> b •∘ (f <$> a))

inDK :: Dual r s d => (K r b -> K r a) -> a --|d|-> b
inDK f = inD (\ a b -> f b •∘ a)

inDV :: Dual r s d => (V s a -> V s b) -> a --|d|-> b
inDV f = inD (\ a b -> b •∘ f a)


-- Elimination

exDK :: Dual r s d => a --|d|-> b -> V s (K r b -> K r a)
exDK f = inV (\ e k -> inK (\ a -> runContext (exD f (inV0 a) k) e))

exDV :: Dual r s d => K r' (V s a -> V s r) -> K r' (a --|d|-> r)
exDV k = inK (\ f -> k • inV . \ a -> runContext (exD f a idK))

evalD :: Dual r s d => s --|d|-> r -> (s -> r)
evalD f = runContext (exD f (inV id) idK)

appD :: Dual r s d => a --|d|-> b -> V s (V s a -> K r **b)
appD f = inV (\ e a -> inK (\ b -> runControl (exD f a b) e))

appD2 :: Dual r s d => a --|d|-> b --|d|-> c -> V s (V s a -> V s b -> K r **c)
appD2 f = inV (\ e a b -> inK (\ c -> runControl (exD f a (inK (\ g -> runControl (exD g b c) e))) e))


-- Computation

(↑) :: Dual r s d => a --|d|-> b -> V s a -> Producer d s b
f ↑ a = f <<< producer a

infixl 7 ↑

(<↑) :: Dual r s d => Conj c => (a `c` _Γ) --|d|-> _Δ -> a -> _Γ --|d|-> _Δ
f <↑ a = f <<< inD' (inlr a)

infixl 7 <↑

(↓) :: Dual r s d => K r b -> a --|d|-> b -> Consumer d r a
k ↓ f = consumer k <<< f

infixl 8 ↓

(↓>) :: (Dual r s d, Disj p) => K r c -> a --|d|-> (b `p` c) -> a --|d|-> b
c ↓> f = inD (\ v k -> (k <••> c) •∘ v) <<< f

infixr 9 ↓>

dnE :: Dual r s d => K r **(a --|d|-> b) -> a --|d|-> b
dnE k = inD (\ a b -> liftKWith (\ _K -> k •• _K (\ f -> exD f a b)))

coerceD :: (Dual k v c, Dual k v d) => c a b -> d a b
coerceD = inD . exD


-- Control context

class Control c where
  control :: (s -> r) -> c r s
  runControl :: c r s -> (s -> r)


newtype ControlT r s m a = ControlT { runControlT :: s -> (a -> m r) -> m r }
  deriving (Functor)

instance Applicative (ControlT r s m) where
  pure a = ControlT $ \ _ k -> k a
  ControlT f <*> ControlT a = ControlT (\ e k -> f e (a e . (k .)))

instance Monad (ControlT r s m) where
  ControlT a >>= f = ControlT (\ e k -> a e (\ a' -> runControlT (f a') e k))

instance MonadTrans (ControlT r s) where
  lift m = ControlT (const (m >>=))


newtype Context r s = Context { runContext :: s -> r }

instance Control Context where
  control = Context
  runControl = runContext


withEnv :: Control c => (s -> c r s) -> c r s
withEnv f = control (runControl =<< f)

withVal :: Control c => (a -> c r s) -> (V s a -> c r s)
withVal f v = withEnv (f . exV v)

liftRunControlWith :: Control c => ((c r s -> r) -> c r s) -> c r s
liftRunControlWith f = withEnv (f . flip runControl)

liftKWith :: Control c => (((a -> c r s) -> K r a) -> c r s) -> c r s
liftKWith f = liftRunControlWith (\ run -> f (inK . (run .)))

(•∘) :: Control c => K r a -> V s a -> c r s
k •∘ v = control (\ e -> k • e ∘ v)

infix 7 •∘

(••) :: Control c => K r a -> a -> c r s
k •• v = control (const (k • v))

infix 7 ••


complete :: (Dual r s d, Control c) => c r s -> Complete d r s
complete = inD . const . const . control . runControl

runComplete :: (Dual r s d, Control c) => Complete d r s -> c r s
runComplete f = control (runControl (exD f idV idK))

type Complete d r s = d s r


inPrd :: Dual r s d => (K r a -> Context r s) -> Producer d s a
inPrd = inD . const

producer :: Dual r s d => V s a -> Producer d s a
producer v = inPrd (•∘ v)

joinl :: Dual r s d => Producer d s (d a b) -> d a b
joinl p = inD (\ a b -> liftKWith (\ _K -> exD p idV (_K (\ f -> exD f a b))))

type Producer d s b = d s b


inCns :: Dual r s d => (V s a -> Context r s) -> Consumer d r a
inCns = inD . fmap const

consumer :: Dual r s d => K r a -> Consumer d r a
consumer k = inCns (k •∘)

type Consumer d r a = d a r
