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
  -- * Composition
, (↓↓)
, (↑↑)
, (↓↑)
  -- * Control context
, Control(..)
, evalControl
, withEnv
, withVal
, liftKWith
, (•∘)
, (••)
, Producer
, Consumer
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
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Profunctor.Applicative
import           Sequoia.Value as V

-- Dual profunctor

newtype D r s a b = D { runD :: V s a -> K r b -> Control r s }

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

_D :: Dual r s d => d a b <-> (V s a -> K r b -> Control r s)
_D = exD <-> inD

class (Cat.Category d, Profunctor d) => Dual r s d | d -> r s where
  inD :: (V s a -> K r b -> Control r s) -> d a b
  exD :: d a b -> V s a -> K r b -> Control r s

instance Dual r s (D r s) where
  inD = D
  exD = runD


-- Construction

inD' :: Dual r s d => (a -> b) -> a --|d|-> b
inD' f = inD (\ a b -> b •∘ (f <$> a))

inDK :: Dual r s d => (K r b -> K r a) -> a --|d|-> b
inDK f = inD (\ a b -> f b •∘ a)

inDV :: Dual r s d => (V s a -> V s b) -> a --|d|-> b
inDV f = inD (\ a b -> b •∘ f a)


-- Elimination

exDK :: Dual r s d => a --|d|-> b -> V s (K r b -> K r a)
exDK f = inV (\ e k -> inK (\ a -> evalControl (exD f (inV0 a) k) e))

exDV :: Dual r s d => K r' (V s a -> V s r) -> K r' (a --|d|-> r)
exDV k = inK (\ f -> k • inV . \ a -> evalControl (exD f a idK))

evalD :: Dual r s d => a --|d|-> r -> Consumer d a
evalD = (idK ↓)


-- Computation

(↑) :: Dual r s d => a --|d|-> b -> V s a -> Producer d b
f ↑ a = inD (const (exD f a))

infixl 7 ↑

(<↑) :: Dual r s d => Conj c => (a `c` _Γ) --|d|-> _Δ -> a -> _Γ --|d|-> _Δ
f <↑ a = f <<< inD' (inlr a)

infixl 7 <↑

(↓) :: Dual r s d => K r b -> a --|d|-> b -> Consumer d a
k ↓ f = inD (const . flip (exD f) k)

infixl 8 ↓

-- FIXME: this is quite limited by the need for the continuation to return locally at r.
(↓>) :: (Dual r s d, Disj p) => K r c -> a --|d|-> (b `p` c) -> a --|d|-> b
c ↓> f = inD (\ v k -> (k <••> c) •∘ v) <<< f

infixr 9 ↓>

dnE :: Dual r s d => K r **(a --|d|-> b) -> a --|d|-> b
dnE k = inD (\ a b -> liftKWith (\ _K -> k •• _K (\ f -> exD f a b)))


-- Composition

(↓↓) :: Dual r s d => Consumer d b -> a --|d|-> b -> Consumer d a
k ↓↓ f = inD (\ a b -> liftKWith (\ _K -> exD f a (_K (flip (exD k) b . inV0))))

infixl 8 ↓↓

(↑↑) :: Dual r s d => a --|d|-> b -> Producer d a -> Producer d b
f ↑↑ v = inD (\ a b -> liftKWith (\ _K -> exD v a (_K (\ a -> exD f (inV0 a) b))))

infixr 7 ↑↑

(↓↑) :: Dual r s d => Consumer d a -> Producer d a -> Control r s
k ↓↑ v = liftKWith (\ _K -> exD v (inV0 ()) (_K (flip (exD k) (inK absurd) . inV0)))

infix 9 ↓↑


-- Control context

newtype Control r s = Control { runControl :: s -> r }

evalControl :: Control r s -> (s -> r)
evalControl (Control v) = (∘ v)

withEnv :: (s -> Control r s) -> Control r s
withEnv f = Control (evalControl =<< f)

withVal :: Value s v => (a -> Control r s) -> (v a -> Control r s)
withVal f v = withEnv (f . exV v)

liftKWith :: Continuation r k => (((a -> Control r s) -> k a) -> Control r s) -> Control r s
liftKWith f = withEnv (\ e -> f (inK . ((`evalControl` e) .)))

(•∘) :: (Continuation r k, Value s v) => k a -> v a -> Control r s
k •∘ v = Control (\ e -> k • e ∘ v)

infix 7 •∘

(••) :: Continuation r k => k a -> a -> Control r s
k •• v = Control (const (k • v))

infix 7 ••


type Producer d b = d () b
type Consumer d a = d a Void
