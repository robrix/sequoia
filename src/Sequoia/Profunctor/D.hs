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
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, (↑)
, (<↑)
, (↓)
, (↓>)
, dnE
  -- * Control context
, Control(..)
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
, producer
, Producer
, consumer
, Consumer
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
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
  coliftA2 f a b = D (\ v k -> withVal ((flip (exD a) k . inV0 <--> flip (exD b) k . inV0) . f) v)


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Dual profunctor abstraction

_D :: Dual k v d => d a b <-> (v a -> k b -> Context (K.Rep k) (V.Rep v))
_D = exD <-> inD

class (K.Representable k, V.Representable v, Cat.Category d, Profunctor d) => Dual k v d | d -> k v where
  inD :: (v a -> k b -> Context (K.Rep k) (V.Rep v)) -> d a b
  exD :: d a b -> v a -> k b -> Context (K.Rep k) (V.Rep v)

instance Dual (K r) (V s) (D r s) where
  inD = D
  exD = runD


-- Construction

inD' :: Dual k v d => (a -> b) -> a --|d|-> b
inD' f = inD (\ a b -> b •∘ (f <$> a))

inDK :: Dual k v d => (k b -> k a) -> a --|d|-> b
inDK f = inD (\ a b -> f b •∘ a)

inDV :: Dual k v d => (v a -> v b) -> a --|d|-> b
inDV f = inD (\ a b -> b •∘ f a)


-- Elimination

exDK :: Dual k v d => a --|d|-> b -> v (k b -> k a)
exDK f = inV (\ e k -> inK (\ a -> runContext (exD f (inV0 a) k) e))

exDV :: (K.Representable k', Dual k v d) => k' (v a -> v (K.Rep k)) -> k' (a --|d|-> K.Rep k)
exDV k = inK (\ f -> k • inV . \ a -> runContext (exD f a idK))

evalD :: Dual k v d => V.Rep v --|d|-> K.Rep k -> (V.Rep v -> K.Rep k)
evalD f = runContext (exD f (inV id) idK)


-- Computation

(↑) :: Dual k v d => a --|d|-> b -> v a -> Producer d v b
f ↑ a = f <<< producer a

infixl 7 ↑

(<↑) :: Dual k v d => Conj c => (a `c` _Γ) --|d|-> _Δ -> a -> _Γ --|d|-> _Δ
f <↑ a = f <<< inD' (inlr a)

infixl 7 <↑

(↓) :: Dual k v d => k b -> a --|d|-> b -> Consumer d k a
k ↓ f = consumer k <<< f

infixl 8 ↓

(↓>) :: (Dual k v d, Disj s) => k c -> a --|d|-> (b `s` c) -> a --|d|-> b
c ↓> f = inD (\ v k -> (k <••> c) •∘ v) <<< f

infixr 9 ↓>

dnE :: Dual k v d => k **(a --|d|-> b) -> a --|d|-> b
dnE k = inD (\ a b -> liftKWith (\ _K -> k •• _K (\ f -> exD f a b)))


-- Control context

class Control c where
  control :: (s -> r) -> c r s
  runControl :: c r s -> (s -> r)


newtype Context r s = Context { runContext :: s -> r }

instance Control Context where
  control = Context
  runControl = runContext


withEnv :: Control c => (s -> c r s) -> c r s
withEnv f = control (runControl =<< f)

withVal :: (Control c, V.Representable v, V.Rep v ~ s) => (a -> c r s) -> (v a -> c r s)
withVal f v = withEnv (f . exV v)

liftRunControlWith :: Control c => ((c r s -> r) -> c r s) -> c r s
liftRunControlWith f = withEnv (f . flip runControl)

liftKWith :: (Control c, K.Representable k, K.Rep k ~ r) => (((a -> c r s) -> k a) -> c r s) -> c r s
liftKWith f = liftRunControlWith (\ run -> f (inK . (run .)))

(•∘) :: (Control c, K.Representable k, K.Rep k ~ r, V.Representable v, V.Rep v ~ s) => k a -> v a -> c r s
k •∘ v = control (\ e -> k • e ∘ v)

infix 7 •∘

(••) :: (Control c, K.Representable k, K.Rep k ~ r) => k a -> a -> c r s
k •• v = control (const (k • v))

infix 7 ••


complete :: (Dual k v d, Control c, K.Rep k ~ r, V.Rep v ~ s) => c r s -> Complete d k v
complete = inD . const . const . control . runControl

runComplete :: (Dual k v d, Control c, K.Rep k ~ r, V.Rep v ~ s) => Complete d k v -> c r s
runComplete f = control (runControl (exD f idV idK))

type Complete d k v = d (V.Rep v) (K.Rep k)


producer :: Dual k v d => v a -> Producer d v a
producer v = inD (\ _ k -> k •∘ v)

type Producer d v b = d (V.Rep v) b


consumer :: Dual k v d => k a -> Consumer d k a
consumer k = inD (\ a _ -> k •∘ a)

type Consumer d k a = d a (K.Rep k)
