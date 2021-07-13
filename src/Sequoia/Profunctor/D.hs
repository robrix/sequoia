{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.D
( -- * Dual profunctor
  D(..)
  -- ** Mixfix notation
, type (--|)
, type (|->)
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
  -- * Control context
, Control(..)
, withEnv
, withVal
, liftKWith
, (••)
, Producer(..)
, Consumer(..)
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Sequoia.Conjunction
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.Applicative
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Value as V

-- Dual profunctor

newtype D r s a b = D { exD :: V s a -> K r b -> Control (K r) (V s) }

instance Profunctor (D r s) where
  dimap f g = D . dimap (rmap f) (lmap (contramap g)) . exD

instance Cat.Category (D r s) where
  id = D (flip (••))
  D f . D g = D (\ a c -> liftKWith (\ _K -> g a (_K (\ b -> f (inV0 b) c))))

instance Functor (D r s c) where
  fmap = rmap

instance Applicative (D r s a) where
  pure a = D (\ _ b -> b •• inV0 a)

  D df <*> D da = D (\ a b -> liftKWith (\ _K -> df a (_K (\ f -> da a (contramap f b)))))

instance Monad (D r s a) where
  D m >>= f = D (\ a c -> liftKWith (\ _K -> m a (_K (\ b -> exD (f b) a c))))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

inD' :: (a -> b) -> a --|D r s|-> b
inD' f = D (\ a b -> b •• (f <$> a))

inDK :: (K r b -> K r a) -> a --|D r s|-> b
inDK f = D (\ a b -> f b •• a)

inDV :: (V s a -> V s b) -> a --|D r s|-> b
inDV f = D (\ a b -> b •• f a)


-- Elimination

exDK :: a --|D r s|-> b -> V s (K r b -> K r a)
exDK f = V (\ e k -> K (\ a -> evalControl (exD f (inV0 a) k) e))

exDV :: K r (V s a -> V s b) -> K r (a --|D b s|-> b)
exDV k = K (\ f -> k • inV . \ a -> evalControl (exD f a idK))

evalD :: a --|D r s|-> r -> V s (K r a)
evalD = (idK ↓)


-- Computation

(↑) :: a --|D r s|-> b -> V s a -> V s (K r (K r b))
f ↑ a = V (K . flip (evalControl . exD f a))

infixl 7 ↑

(<↑) :: Conj c => (a `c` _Γ) --|D r s|-> _Δ -> a -> _Γ --|D r s|-> _Δ
f <↑ a = f <<< inD' (inlr a)

infixl 7 <↑

(↓) :: K r b -> a --|D r s|-> b -> V s (K r a)
k ↓ f = V (\ e -> K (\ a -> evalControl (exD f (inV0 a) k) e))

infixl 8 ↓

-- FIXME: this is quite limited by the need for the continuation to return locally at r.
(↓>) :: Disj d => K r c -> a --|D r s|-> (b `d` c) -> a --|D r s|-> b
c ↓> f = D (\ v k -> (k <••> c) •• v) <<< f

infixr 9 ↓>


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

(••) :: (K.Representable k, V.Representable v) => k a -> v a -> Control k v
k •• v = control (\ e -> k • e ∘ v)

infix 7 ••


newtype Producer r s b = Producer { runProducer :: K r b -> Control (K r) (V s) }

instance Functor (Producer r s) where
  fmap f = Producer . lmap (contramap f) . runProducer

instance Applicative (Producer r s) where
  pure = Producer . fmap (control . const) . flip (•)
  Producer f <*> Producer a = Producer (\ k -> liftKWith (\ _K -> f (_K (a . (k •<<)))))

instance Monad (Producer r s) where
  Producer m >>= f = Producer (\ k -> liftKWith (\ _K -> m (_K ((`runProducer` k) . f))))


newtype Consumer r s a = Consumer { runConsumer :: V s a -> Control (K r) (V s) }

instance Contravariant (Consumer r s) where
  contramap f = Consumer . lmap (fmap f) . runConsumer

instance K.Representable (Consumer r s) where
  type Rep (Consumer r s) = Control (K r) (V s)
  tabulate = Consumer . withVal
  index (Consumer r) = r . inV0

instance Contrapply (Consumer r s) where
  contraliftA2 f (Consumer a) (Consumer b) = Consumer (withVal ((a . inV0 <--> b . inV0) . f))

instance Contrapplicative (Consumer r s)
