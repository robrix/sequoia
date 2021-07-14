{-# LANGUAGE QuantifiedConstraints #-}
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

_D :: Dual d => d r s a b <-> (V s a -> K r b -> Context r s)
_D = exD <-> inD

class (forall r s . Cat.Category (d r s), forall r s . Profunctor (d r s)) => Dual d where
  inD :: (V s a -> K r b -> Context r s) -> d r s a b
  exD :: d r s a b -> V s a -> K r b -> Context r s

instance Dual D where
  inD = D
  exD = runD


-- Construction

inD' :: Dual d => (a -> b) -> a --|d r s|-> b
inD' f = inD (\ a b -> b •∘ (f <$> a))

inDK :: Dual d => (K r b -> K r a) -> a --|d r s|-> b
inDK f = inD (\ a b -> f b •∘ a)

inDV :: Dual d => (V s a -> V s b) -> a --|d r s|-> b
inDV f = inD (\ a b -> b •∘ f a)


-- Elimination

exDK :: Dual d => a --|d r s|-> b -> V s (K r b -> K r a)
exDK f = inV (\ e k -> inK (\ a -> runContext (exD f (inV0 a) k) e))

exDV :: Dual d => K r' (V s a -> V s r) -> K r' (a --|d r s|-> r)
exDV k = inK (\ f -> k • inV . \ a -> runContext (exD f a idK))

evalD :: Dual d => s --|d r s|-> r -> (s -> r)
evalD f = runContext (exD f (inV id) idK)


-- Computation

(↑) :: Dual d => a --|d r s|-> b -> V s a -> Producer d r s b
f ↑ a = f <<< producer a

infixl 7 ↑

(<↑) :: Dual d => Conj c => (a `c` _Γ) --|d r s|-> _Δ -> a -> _Γ --|d r s|-> _Δ
f <↑ a = f <<< inD' (inlr a)

infixl 7 <↑

(↓) :: Dual d => K r b -> a --|d r s|-> b -> Consumer d r s a
k ↓ f = consumer k <<< f

infixl 8 ↓

(↓>) :: (Dual d, Disj p) => K r c -> a --|d r s|-> (b `p` c) -> a --|d r s|-> b
c ↓> f = inD (\ v k -> (k <••> c) •∘ v) <<< f

infixr 9 ↓>

dnE :: Dual d => K r **(a --|d r s|-> b) -> a --|d r s|-> b
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


complete :: (Dual d, Control c) => c r s -> Complete d r s
complete = inD . const . const . control . runControl

runComplete :: (Dual d, Control c) => Complete d r s -> c r s
runComplete f = control (runControl (exD f idV idK))

type Complete d r s = d r s s r


producer :: Dual d => V s a -> Producer d r s a
producer v = inD (\ _ k -> k •∘ v)

type Producer d r s b = d r s s b


consumer :: Dual d => K r a -> Consumer d r s a
consumer k = inD (\ a _ -> k •∘ a)

type Consumer d r s a = d r s a r
