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

newtype D r s a b = D { exD :: V s a -> K r b -> (s -> r) }

instance Profunctor (D r s) where
  dimap f g = D . dimap (rmap f) (lmap (contramap g)) . exD

instance Cat.Category (D r s) where
  id = D (\ a b e -> b • e ∘ a)
  D f . D g = D (\ a c e -> g a (K (\ b -> f (inV0 b) c e)) e)

instance Functor (D r s c) where
  fmap = rmap

instance Applicative (D r s a) where
  pure a = D (\ _ b _ -> b • a)

  D df <*> D da = D (\ a b e -> df a (K (\ f -> da a (contramap f b) e)) e)

instance Monad (D r s a) where
  D m >>= f = D (\ a c e -> m a (K (\ b -> exD (f b) a c e)) e)


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

inD' :: (a -> b) -> a --|D r s|-> b
inD' f = D (\ a b e -> b • f (e ∘ a))

inDK :: (K r b -> K r a) -> a --|D r s|-> b
inDK f = D (\ a b e -> f b • e ∘ a)

inDV :: (V s a -> V s b) -> a --|D r s|-> b
inDV f = D (\ a b e -> b • e ∘ f a)


-- Elimination

exDK :: a --|D r s|-> b -> V s (K r b -> K r a)
exDK f = V (\ e k -> K (\ a -> exD f (inV0 a) k e))

exDV :: K r (V s a -> V s b) -> K r (a --|D b s|-> b)
exDV k = K (\ f -> k • inV . \ a -> exD f a idK)

evalD :: a --|D r s|-> r -> V s (K r a)
evalD = (idK ↓)


-- Computation

(↑) :: a --|D r s|-> b -> V s a -> V s (K r (K r b))
f ↑ a = V (K . flip (exD f a))

infixl 7 ↑

(<↑) :: Conj c => (a `c` _Γ) --|D r s|-> _Δ -> a -> _Γ --|D r s|-> _Δ
f <↑ a = f <<< inD' (inlr a)

infixl 7 <↑

(↓) :: K r b -> a --|D r s|-> b -> V s (K r a)
k ↓ f = V (\ e -> K (\ a -> exD f (inV0 a) k e))

infixl 8 ↓

-- FIXME: this is quite limited by the need for the continuation to return locally at r.
(↓>) :: Disj d => K r c -> a --|D r s|-> (b `d` c) -> a --|D r s|-> b
c ↓> f = D (\ v k e -> (k <••> c) • e ∘ v) <<< f

infixr 9 ↓>


-- Control context

newtype Control r s = Control { runControl :: s -> r }

withEnv :: (s -> Control r s) -> Control r s
withEnv f = Control (runControl =<< f)

withVal :: (a -> Control r s) -> (V s a -> Control r s)
withVal f v = withEnv (f . exV v)

liftKWith :: (((a -> Control r s) -> K r a) -> Control r s) -> Control r s
liftKWith f = withEnv (\ e -> f (K . ((`runControl` e) .)))

(••) :: K r a -> V s a -> Control r s
k •• v = Control (\ e -> k • e ∘ v)

infix 7 ••


newtype Producer r s b = Producer { runProducer :: K r b -> Control r s }

instance Functor (Producer r s) where
  fmap f = Producer . lmap (contramap f) . runProducer

instance Applicative (Producer r s) where
  pure = Producer . fmap (Control . const) . flip (•)
  Producer f <*> Producer a = Producer (\ k -> liftKWith (\ _K -> f (_K (a . (k •<<)))))

instance Monad (Producer r s) where
  Producer m >>= f = Producer (\ k -> liftKWith (\ _K -> m (_K ((`runProducer` k) . f))))


newtype Consumer r s a = Consumer { runConsumer :: V s a -> Control r s }

instance Contravariant (Consumer r s) where
  contramap f = Consumer . lmap (fmap f) . runConsumer

instance K.Representable (Consumer r s) where
  type Rep (Consumer r s) = Control r s
  tabulate = Consumer . withVal
  index (Consumer r) = r . inV0

instance Contrapply (Consumer r s) where
  contraliftA2 f (Consumer a) (Consumer b) = Consumer (withVal ((a . inV0 <--> b . inV0) . f))

instance Contrapplicative (Consumer r s)
