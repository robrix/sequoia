{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
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
  -- * Composition
, (↓↓)
, (↑↑)
, (↓↑)
  -- * Control context
, Control(..)
, evalControl
, control
, withEnv
, withVal
, liftKWith
, (•∘)
, (••)
, Producer(..)
, coercePD
, Consumer(..)
, coerceCD
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Void
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

_D :: Dual k v d => d a b <-> (v a -> k b -> Control k v)
_D = exD <-> inD

class (K.Representable k, V.Representable v, Cat.Category d, Profunctor d) => Dual k v d | d -> k v where
  inD :: (v a -> k b -> Control k v) -> d a b
  exD :: d a b -> v a -> k b -> Control k v

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
exDK f = inV (\ e k -> inK (\ a -> evalControl (exD f (inV0 a) k) e))

exDV :: (K.Representable k', Dual k v d) => k' (v a -> v (K.Rep k)) -> k' (a --|d|-> K.Rep k)
exDV k = inK (\ f -> k • inV . \ a -> evalControl (exD f a idK))

evalD :: Dual k v d => a --|d|-> K.Rep k -> Consumer k v a
evalD = (idK ↓)


-- Computation

(↑) :: Dual k v d => a --|d|-> b -> v a -> Producer k v b
f ↑ a = Producer (D (const (exD f a)))

infixl 7 ↑

(<↑) :: Dual k v d => Conj c => (a `c` _Γ) --|d|-> _Δ -> a -> _Γ --|d|-> _Δ
f <↑ a = f <<< inD' (inlr a)

infixl 7 <↑

(↓) :: Dual k v d => k b -> a --|d|-> b -> Consumer k v a
k ↓ f = Consumer (\ a _ -> exD f a k)

infixl 8 ↓

-- FIXME: this is quite limited by the need for the continuation to return locally at r.
(↓>) :: (Dual k v d, Disj s) => k c -> a --|d|-> (b `s` c) -> a --|d|-> b
c ↓> f = inD (\ v k -> (k <••> c) •∘ v) <<< f

infixr 9 ↓>

dnE :: Dual k v d => k **(a --|d|-> b) -> a --|d|-> b
dnE k = inD (\ a b -> liftKWith (\ _K -> k •• _K (\ f -> exD f a b)))


-- Composition

(↓↓) :: Dual k v d => Consumer k v b -> a --|d|-> b -> Consumer k v a
Consumer k ↓↓ f = Consumer (\ a b -> liftKWith (\ _K -> exD f a (_K ((`k` b) . inV0))))

infixl 8 ↓↓

(↑↑) :: Dual k v d => a --|d|-> b -> Producer k v a -> Producer k v b
f ↑↑ Producer v = Producer (D (\ a b -> liftKWith (\ _K -> exD v a (_K (\ a -> exD f (inV0 a) b)))))

infixr 7 ↑↑

(↓↑) :: (K.Representable k, V.Representable v) => Consumer k v a -> Producer k v a -> Control k v
Consumer k ↓↑ Producer v = liftKWith (\ _K -> exD v (inV0 ()) (_K ((`k` inK absurd) . inV0)))

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


newtype Producer k v b = Producer { runProducer :: () --|D k v|-> b }
  deriving (Functor)

instance (K.Representable k, V.Representable v) => Applicative (Producer k v) where
  pure = Producer . D . const . fmap (control . const) . flip (•)
  Producer f <*> Producer a = Producer (D (\ v k -> liftKWith (\ _K -> exD f v (_K (exD a v . (k •<<))))))

instance (K.Representable k, V.Representable v) => Monad (Producer k v) where
  Producer m >>= f = Producer (D (\ v k -> liftKWith (\ _K -> exD m v (_K (\ a -> exD (runProducer (f a)) v k)))))

coercePD :: Dual k v d => Producer k v b -> d () b
coercePD = inD . exD . runProducer


newtype Consumer k v a = Consumer { runConsumer :: v a -> k Void -> Control k v }

instance Functor v => Contravariant (Consumer k v) where
  contramap f = Consumer . lmap (fmap f) . runConsumer

instance (K.Representable k, V.Representable v) => K.Representable (Consumer k v) where
  type Rep (Consumer k v) = Control k v
  tabulate = Consumer . fmap const . withVal
  index (Consumer r) = (`r` inK absurd) . inV0

instance (K.Representable k, V.Representable v) => Contrapply (Consumer k v) where
  contraliftA2 f (Consumer a) (Consumer b) = Consumer (\ v k -> withVal (((`a` k) . inV0 <--> (`b` k) . inV0) . f) v)

instance (K.Representable k, V.Representable v) => Contrapplicative (Consumer k v)

coerceCD :: Dual k v d => Consumer k v a -> d a Void
coerceCD (Consumer r) = inD r
