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
, KFor
, VFor
, Context(..)
, withEnv
, withVal
, liftRunContextWith
, liftKWith
, (•∘)
, (••)
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
import           Sequoia.Profunctor.Applicative
import           Sequoia.Value as V

-- Dual profunctor

newtype D k v a b = D { runD :: v a -> k b -> Context (K.Rep k) (V.Rep v) }

instance (Contravariant k, Functor v) => Profunctor (D k v) where
  dimap f g = D . dimap (fmap f) (lmap (contramap g)) . runD

instance (K.Representable k, V.Representable v) => Cat.Category (D k v) where
  id = D (flip (•∘))
  D f . D g = D (\ a c -> liftKWith (\ _K -> g a (_K (\ b -> f (inV0 b) c))))

instance Contravariant k => Functor (D k v c) where
  fmap f = D . fmap (lmap (contramap f)) . runD

instance (K.Representable k, V.Representable v) => Applicative (D k v a) where
  pure a = D (\ _ b -> b •• a)

  D df <*> D da = D (\ a b -> liftKWith (\ _K -> df a (_K (\ f -> da a (contramap f b)))))

instance (K.Representable k, V.Representable v) => Monad (D k v a) where
  D m >>= f = D (\ a c -> liftKWith (\ _K -> m a (_K (\ b -> runD (f b) a c))))

instance (K.Representable k, V.Representable v) => Coapply (D k v) where
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

instance (K.Representable k, V.Representable v) => Dual k v (D k v) where
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
  type R c
  type S c

  control :: (S c -> R c) -> c
  runControl :: c -> (S c -> R c)

type KFor k c = (K.Representable k, K.Rep k ~ R c)
type VFor v c = (V.Representable v, V.Rep v ~ S c)


newtype Context r s = Context { runContext :: s -> r }

instance Control (Context r s) where
  type R (Context r s) = r
  type S (Context r s) = s
  control = Context
  runControl = runContext


withEnv :: Control c => (S c -> c) -> c
withEnv f = control (runControl =<< f)

withVal :: (Control c, VFor v c) => (a -> c) -> (v a -> c)
withVal f v = withEnv (f . exV v)

liftRunContextWith :: ((Context r s -> r) -> Context r s) -> Context r s
liftRunContextWith f = withEnv (f . flip runContext)

liftKWith :: K.Representable k => (((a -> Context (K.Rep k) s) -> k a) -> Context (K.Rep k) s) -> Context (K.Rep k) s
liftKWith f = liftRunContextWith (\ run -> f (inK . (run .)))

(•∘) :: (K.Representable k, V.Representable v) => k a -> v a -> Context (K.Rep k) (V.Rep v)
k •∘ v = Context (\ e -> k • e ∘ v)

infix 7 •∘

(••) :: K.Representable k => k a -> a -> Context (K.Rep k) s
k •• v = Context (const (k • v))

infix 7 ••


type Complete d k v = d (V.Rep v) (K.Rep k)


producer :: Dual k v d => v a -> Producer d v a
producer v = inD (\ _ k -> k •∘ v)

type Producer d v b = d (V.Rep v) b


consumer :: Dual k v d => k a -> Consumer d k a
consumer k = inD (\ a _ -> k •∘ a)

type Consumer d k a = d a (K.Rep k)
