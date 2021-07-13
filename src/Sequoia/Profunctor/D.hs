{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.D
( -- * Dual profunctor
  D(..)
  -- ** Mixfix notation
, type (--|)
, type (|->)
  -- ** Dual profunctor abstraction
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
  -- * Composition
, (↓↓)
, (↑↑)
, (↓↑)
  -- * Control context
, Control(..)
, withEnv
, withVal
, liftKWith
, (•∘)
, (••)
, Producer(..)
, Consumer(..)
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Sequoia.Bijection
import           Sequoia.Conjunction
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.Applicative
import           Sequoia.Value as V

-- Dual profunctor

newtype D k v a b = D { runD :: v a -> k b -> Control k v }

instance (Contravariant k, Functor v) => Profunctor (D k v) where
  dimap f g = D . dimap (fmap f) (lmap (contramap g)) . runD

instance (K.Representable k, V.Representable v) => Cat.Category (D k v) where
  id = D (flip (•∘))
  D f . D g = D (\ a c -> liftKWith (\ _K -> g a (_K (\ b -> f (inV0 b) c))))

instance Contravariant k => Functor (D k v c) where
  fmap f = D . fmap (lmap (contramap f)) . runD

instance (K.Representable k, V.Representable v) => Applicative (D k v a) where
  pure a = D (\ _ b -> b •∘ inV0 a)

  D df <*> D da = D (\ a b -> liftKWith (\ _K -> df a (_K (\ f -> da a (contramap f b)))))

instance (K.Representable k, V.Representable v) => Monad (D k v a) where
  D m >>= f = D (\ a c -> liftKWith (\ _K -> m a (_K (\ b -> runD (f b) a c))))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Dual profunctor abstraction

class (K.Representable k, V.Representable v) => Dual k v d | d -> k v where
  _D :: d k v <-> (v a -> k b -> Control k v)
  _D = exD <-> inD

  inD :: (v a -> k b -> Control k v) -> d k v
  exD :: d k v -> v a -> k b -> Control k v


-- Construction

inD' :: (K.Representable k, V.Representable v) => (a -> b) -> a --|D k v|-> b
inD' f = D (\ a b -> b •∘ (f <$> a))

inDK :: (K.Representable k, V.Representable v) => (k b -> k a) -> a --|D k v|-> b
inDK f = D (\ a b -> f b •∘ a)

inDV :: (K.Representable k, V.Representable v) => (v a -> v b) -> a --|D k v|-> b
inDV f = D (\ a b -> b •∘ f a)


-- Elimination

exDK :: (K.Representable k, V.Representable v) => a --|D k v|-> b -> v (k b -> k a)
exDK f = inV (\ e k -> inK (\ a -> evalControl (runD f (inV0 a) k) e))

exDV :: (K.Representable k, K.Representable k', V.Representable v) => k (v a -> v (K.Rep k')) -> k (a --|D k' v|-> K.Rep k')
exDV k = inK (\ f -> k • inV . \ a -> evalControl (runD f a idK))

evalD :: K.Representable k => a --|D k v|-> K.Rep k -> Consumer k v a
evalD = (idK ↓)


-- Computation

(↑) :: a --|D k v|-> b -> v a -> Producer k v b
f ↑ a = Producer (runD f a)

infixl 7 ↑

(<↑) :: (K.Representable k, V.Representable v) => Conj c => (a `c` _Γ) --|D k v|-> _Δ -> a -> _Γ --|D k v|-> _Δ
f <↑ a = f <<< inD' (inlr a)

infixl 7 <↑

(↓) :: k b -> a --|D k v|-> b -> Consumer k v a
k ↓ f = Consumer (flip (runD f) k)

infixl 8 ↓

-- FIXME: this is quite limited by the need for the continuation to return locally at r.
(↓>) :: (K.Representable k, V.Representable v) => Disj d => k c -> a --|D k v|-> (b `d` c) -> a --|D k v|-> b
c ↓> f = D (\ v k -> (k <••> c) •∘ v) <<< f

infixr 9 ↓>

dnE :: (K.Representable k, V.Representable v) => k **(a --|D k v|-> b) -> a --|D k v|-> b
dnE k = D (\ a b -> liftKWith (\ _K -> k •• _K (\ f -> runD f a b)))


-- Composition

(↓↓) :: (K.Representable k, V.Representable v) => Consumer k v b -> a --|D k v|-> b -> Consumer k v a
Consumer k ↓↓ f = Consumer (\ a -> liftKWith (\ _K -> runD f a (_K (k . inV0))))

infixl 8 ↓↓

(↑↑) :: (K.Representable k, V.Representable v) => a --|D k v|-> b -> Producer k v a -> Producer k v b
f ↑↑ Producer v = Producer (\ b -> liftKWith (\ _K -> v (_K (\ a -> runD f (inV0 a) b))))

infixr 7 ↑↑

(↓↑) :: (K.Representable k, V.Representable v) => Consumer k v a -> Producer k v a -> Control k v
Consumer k ↓↑ Producer v = liftKWith (\ _K -> v (_K (k . inV0)))

infix 9 ↓↑


-- Control context

newtype Control k v = Control { runControl :: forall x . v (k x) }

evalControl :: (K.Representable k, V.Representable v) => Control k v -> (V.Rep v -> K.Rep k)
evalControl (Control v) = (• ()) . (∘ v)

control :: (K.Representable k, V.Representable v) => (V.Rep v -> K.Rep k) -> Control k v
control f = Control (inV (inK . const . f))

withEnv :: (K.Representable k, V.Representable v) => (V.Rep v -> Control k v) -> Control k v
withEnv f = control (evalControl =<< f)

withVal :: (K.Representable k, V.Representable v) => (a -> Control k v) -> (v a -> Control k v)
withVal f v = withEnv (f . exV v)

liftKWith :: (K.Representable k, V.Representable v) => (((a -> Control k v) -> k a) -> Control k v) -> Control k v
liftKWith f = withEnv (\ e -> f (inK . ((`evalControl` e) .)))

(•∘) :: (K.Representable k, V.Representable v) => k a -> v a -> Control k v
k •∘ v = control (\ e -> k • e ∘ v)

infix 7 •∘

(••) :: (K.Representable k, V.Representable v) => k a -> a -> Control k v
k •• v = control (const (k • v))

infix 7 ••


newtype Producer k v b = Producer { runProducer :: k b -> Control k v }

instance Contravariant k => Functor (Producer k v) where
  fmap f = Producer . lmap (contramap f) . runProducer

instance (K.Representable k, V.Representable v) => Applicative (Producer k v) where
  pure = Producer . fmap (control . const) . flip (•)
  Producer f <*> Producer a = Producer (\ k -> liftKWith (\ _K -> f (_K (a . (k •<<)))))

instance (K.Representable k, V.Representable v) => Monad (Producer k v) where
  Producer m >>= f = Producer (\ k -> liftKWith (\ _K -> m (_K ((`runProducer` k) . f))))


newtype Consumer k v a = Consumer { runConsumer :: v a -> Control k v }

instance Functor v => Contravariant (Consumer k v) where
  contramap f = Consumer . lmap (fmap f) . runConsumer

instance (K.Representable k, V.Representable v) => K.Representable (Consumer k v) where
  type Rep (Consumer k v) = Control k v
  tabulate = Consumer . withVal
  index (Consumer r) = r . inV0

instance (K.Representable k, V.Representable v) => Contrapply (Consumer k v) where
  contraliftA2 f (Consumer a) (Consumer b) = Consumer (withVal ((a . inV0 <--> b . inV0) . f))

instance (K.Representable k, V.Representable v) => Contrapplicative (Consumer k v)
