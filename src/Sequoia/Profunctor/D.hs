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
  -- * Continuations
, liftCont
, lowerCont
, Cont(..)
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Sequoia.Bijection
import           Sequoia.Conjunction
import           Sequoia.Continuation as K hiding (Cont(..))
import           Sequoia.Disjunction
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Profunctor.Applicative
import           Sequoia.Value as V

-- Dual profunctor

newtype D e r a b = D { runD :: V e a -> K r b -> Context e r }

instance Profunctor (D e r) where
  dimap f g = D . dimap (fmap f) (lmap (contramap g)) . runD

instance Strong (D e r) where
  first'  (D r) = D (\ a b -> withVal (\ (a, c) -> r (inV0 a) (contramap (,c) b)) a)
  second' (D r) = D (\ a b -> withVal (\ (c, a) -> r (inV0 a) (contramap (c,) b)) a)

instance Choice (D e r) where
  left'  (D r) = D (\ a b -> withVal ((`r` inlK b) . inV0 <--> (inrK b ••)) a)
  right' (D r) = D (\ a b -> withVal ((inlK b ••) <--> (`r` inrK b) . inV0) a)

instance Traversing (D e r) where
  wander traverse r = D (\ s t -> withVal (\ s -> exD (traverse ((r ↑) . inV0) s) idV t) s)

instance Cat.Category (D e r) where
  id = D (flip (•∘))
  D f . D g = D (\ a c -> liftKWith (\ _K -> g a (_K (\ b -> f (inV0 b) c))))

instance Functor (D e r c) where
  fmap f = D . fmap (lmap (contramap f)) . runD

instance Applicative (D e r a) where
  pure a = D (\ _ b -> b •• a)

  D df <*> D da = D (\ a b -> liftKWith (\ _K -> df a (_K (\ f -> da a (contramap f b)))))

instance Monad (D e r a) where
  D m >>= f = D (\ a c -> liftKWith (\ _K -> m a (_K (\ b -> runD (f b) a c))))

instance Coapply (D e r) where
  coliftA2 f a b = D (\ v k -> withEnv ((flip (exD a) k <∘∘> flip (exD b) k) (f <$> v)))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Dual profunctor abstraction

_D :: Dual e r d => d a b <-> (V e a -> K r b -> Context e r)
_D = exD <-> inD

class (Cat.Category d, Profunctor d) => Dual e r d | d -> e r where
  inD :: (V e a -> K r b -> Context e r) -> d a b
  exD :: d a b -> V e a -> K r b -> Context e r

instance Dual e r (D e r) where
  inD = D
  exD = runD


-- Construction

inD' :: Dual e r d => (a -> b) -> a --|d|-> b
inD' f = inD (\ a b -> b •∘ (f <$> a))

inDK :: Dual e r d => (K r b -> K r a) -> a --|d|-> b
inDK f = inD (\ a b -> f b •∘ a)

inDV :: Dual e r d => (V e a -> V e b) -> a --|d|-> b
inDV f = inD (\ a b -> b •∘ f a)


-- Elimination

exDK :: Dual e r d => a --|d|-> b -> V e (K r b -> K r a)
exDK f = inV (\ e k -> inK (\ a -> runContext (exD f (inV0 a) k) e))

exDV :: Dual e r d => K r' (V e a -> V e r) -> K r' (a --|d|-> r)
exDV k = inK (\ f -> k • inV . \ a -> runContext (exD f a idK))

evalD :: Dual e r d => e --|d|-> r -> (e -> r)
evalD f = runContext (exD f (inV id) idK)

appD :: Dual e r d => a --|d|-> b -> V e (V e a -> K r **b)
appD f = inV (\ e a -> inK (\ b -> runControl (exD f a b) e))

appD2 :: Dual e r d => a --|d|-> b --|d|-> c -> V e (V e a -> V e b -> K r **c)
appD2 f = inV (\ e a b -> inK (\ c -> runControl (exD f a (inK (\ g -> runControl (exD g b c) e))) e))


-- Computation

(↑) :: Dual e r d => a --|d|-> b -> V e a -> Producer d s b
f ↑ a = f <<< producer a

infixl 7 ↑

(<↑) :: Dual e r d => Conj c => (a `c` _Γ) --|d|-> _Δ -> a -> _Γ --|d|-> _Δ
f <↑ a = f <<< inD' (inlr a)

infixl 7 <↑

(↓) :: Dual e r d => K r b -> a --|d|-> b -> Consumer d r a
k ↓ f = consumer k <<< f

infixl 8 ↓

(↓>) :: (Dual e r d, Disj p) => K r c -> a --|d|-> (b `p` c) -> a --|d|-> b
c ↓> f = inD (\ v k -> (k <••> c) •∘ v) <<< f

infixr 9 ↓>

dnE :: Dual e r d => K r **(a --|d|-> b) -> a --|d|-> b
dnE k = inD (\ a b -> liftKWith (\ _K -> k •• _K (\ f -> exD f a b)))

coerceD :: (Dual k v c, Dual k v d) => c a b -> d a b
coerceD = inD . exD


-- Control context

class Control e r c | c -> e r where
  control :: (e -> r) -> c
  runControl :: c -> (e -> r)


newtype Context e r = Context { runContext :: e -> r }

instance Control e r (Context e r) where
  control = Context
  runControl = runContext

instance Control e r (D e r e r) where
  control = complete . Context
  runControl = runContext . runComplete


withEnv :: Control e r c => (e -> c) -> c
withEnv f = control (runControl =<< f)

withVal :: (Control e r c, V.Representable v, V.Rep v ~ e) => (a -> c) -> (v a -> c)
withVal f v = withEnv (f . exV v)

liftRunControlWith :: Control e r c => ((c -> r) -> c) -> c
liftRunControlWith f = withEnv (f . flip runControl)

liftKWith :: (Control e r c, K.Representable k, K.Rep k ~ r) => (((a -> c) -> k a) -> c) -> c
liftKWith f = liftRunControlWith (\ run -> f (inK . (run .)))

(•∘) :: (Control e r c, K.Representable k, K.Rep k ~ r, V.Representable v, V.Rep v ~ e) => k a -> v a -> c
k •∘ v = control (\ e -> k • e ∘ v)

infix 7 •∘

(••) :: (Control e r c, K.Representable k, K.Rep k ~ r) => k a -> a -> c
k •• v = control (const (k • v))

infix 7 ••


complete :: (Dual e r d, Control e r c) => c -> Complete d e r
complete = inD . const . const . control . runControl

runComplete :: (Dual e r d, Control e r c) => Complete d e r -> c
runComplete f = control (runControl (exD f idV idK))

type Complete d e r = d e r


inPrd :: Dual e r d => (K r a -> Context e r) -> Producer d s a
inPrd = inD . const

producer :: (Dual e r d, V.Representable v, V.Rep v ~ e) => v a -> Producer d s a
producer v = inPrd (•∘ v)

joinl :: Dual e r d => Producer d e (d a b) -> d a b
joinl p = inD (\ a b -> liftKWith (\ _K -> exD p idV (_K (\ f -> exD f a b))))

type Producer d s b = d s b


inCns :: Dual e r d => (V e a -> Context e r) -> Consumer d r a
inCns = inD . fmap const

consumer :: (Dual e r d, K.Representable k, K.Rep k ~ r) => k a -> Consumer d r a
consumer k = inCns (k •∘)

type Consumer d r a = d a r


-- Continuations

liftCont :: K r a -> Cont e r a
liftCont k = Cont (k •∘)

lowerCont :: Cont e r a -> V e (K r a)
lowerCont (Cont r) = V $ \ e -> K (\ a -> runControl (r (inV0 a)) e)

newtype Cont e r a = Cont { runCont :: V e a -> Context e r }

instance Contravariant (Cont e r) where
  contramap f = Cont . lmap (fmap f) . runCont

instance K.Representable (Cont e r) where
  type Rep (Cont e r) = Context e r
  tabulate f = Cont (\ v -> withVal id (f <$> v))
  index (Cont r) a = r (inV0 a)

instance Continuation r (Cont e r) where
