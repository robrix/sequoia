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
, runD
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, (↑)
, (↓)
, dnE
, coerceD
  -- * Control context
, (•∘)
, Control(..)
, inPrd
, producer
, joinl
, consumer
, inCns
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Sequoia.Bijection
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Profunctor.Applicative
import           Sequoia.Value as V

-- Dual profunctor

newtype D e r a b = D { getD :: V e a -> K r b -> Control e r }

instance Profunctor (D e r) where
  dimap f g = D . dimap (fmap f) (lmap (contramap g)) . getD

instance Strong (D e r) where
  first'  (D r) = D (\ a b -> val (\ (a, c) -> r (inV0 a) (contramap (,c) b)) a)
  second' (D r) = D (\ a b -> val (\ (c, a) -> r (inV0 a) (contramap (c,) b)) a)

instance Choice (D e r) where
  left'  (D r) = D (\ a b -> val ((`r` inlK b) . inV0 <--> (inrK b ••)) a)
  right' (D r) = D (\ a b -> val ((inlK b ••) <--> (`r` inrK b) . inV0) a)

instance Traversing (D e r) where
  wander traverse r = D (\ s t -> val (\ s -> exD (traverse ((r ↑) . inV0) s) idV t) s)

instance Cat.Category (D e r) where
  id = D (flip (•∘))
  D f . D g = D (\ a c -> cont (\ _K -> g a (_K (\ b -> f (inV0 b) c))))

instance Functor (D e r c) where
  fmap f = D . fmap (lmap (contramap f)) . getD

instance Applicative (D e r a) where
  pure a = D (\ _ b -> b •• a)

  D df <*> D da = D (\ a b -> cont (\ _K -> df a (_K (\ f -> da a (contramap f b)))))

instance Monad (D e r a) where
  D m >>= f = D (\ a c -> cont (\ _K -> m a (_K (\ b -> getD (f b) a c))))

instance Coapply (D e r) where
  coliftA2 f a b = D (\ v k -> env ((flip (exD a) k <∘∘> flip (exD b) k) (f <$> v)))

instance Env e (D e r a b) where
  env f = D (\ v k -> env (runD v k . f))

instance Res r (D e r a b) where
  res = D . const . const . res
  liftRes f = D (\ v k -> liftRes (\ run -> exD (f (run . runD v k)) v k))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Dual profunctor abstraction

_D :: Dual e r d => d a b <-> (V e a -> K r b -> Control e r)
_D = exD <-> inD

class (Cat.Category d, Profunctor d) => Dual e r d | d -> e r where
  inD :: (V e a -> K r b -> Control e r) -> d a b
  exD :: d a b -> V e a -> K r b -> Control e r

instance Dual e r (D e r) where
  inD = D
  exD = getD


-- Construction

inD' :: Dual e r d => (a -> b) -> a --|d|-> b
inD' f = inD (\ a b -> b •∘ (f <$> a))

inDK :: Dual e r d => (K r b -> K r a) -> a --|d|-> b
inDK f = inD (\ a b -> f b •∘ a)

inDV :: Dual e r d => (V e a -> V e b) -> a --|d|-> b
inDV f = inD (\ a b -> b •∘ f a)


-- Elimination

exDK :: Dual e r d => a --|d|-> b -> V e (K r b -> K r a)
exDK f = inV (\ e k -> inK (\ a -> getControl (exD f (inV0 a) k) e))

exDV :: Dual e r d => K r' (V e a -> V e r) -> K r' (a --|d|-> r)
exDV k = inK (\ f -> k • inV . \ a -> getControl (exD f a idK))

evalD :: Dual e r d => e --|d|-> r -> (e -> r)
evalD f = getControl (exD f (inV id) idK)

appD :: Dual e r d => a --|d|-> b -> V e (V e a -> K r **b)
appD f = inV (\ e a -> inK (\ b -> getControl (exD f a b) e))

appD2 :: Dual e r d => a --|d|-> b --|d|-> c -> V e (V e a -> V e b -> K r **c)
appD2 f = inV (\ e a b -> inK (\ c -> getControl (exD f a (inK (\ g -> getControl (exD g b c) e))) e))

runD :: Dual e r d => V e a -> K r b -> a --|d|-> b -> Control e r
runD v k f = exD f v k


-- Computation

(↑) :: Dual e r d => a --|d|-> b -> V e a -> d s|-> b
f ↑ a = f <<< producer a

infixl 7 ↑

(↓) :: Dual e r d => K r b -> a --|d|-> b -> a --|d|-> r
k ↓ f = consumer k <<< f

infixl 8 ↓

dnE :: Dual e r d => K r **(a --|d|-> b) -> a --|d|-> b
dnE k = inD (\ a b -> cont (\ _K -> k •• _K (\ f -> exD f a b)))

coerceD :: (Dual k v c, Dual k v d) => c a b -> d a b
coerceD = inD . exD


-- Control context

(•∘) :: (Env (V.Rep v) c, V.Representable v, Res (K.Rep k) c, K.Representable k) => k a -> v a -> c
k •∘ v = env (\ e -> res (k • e ∘ v))

infix 7 •∘


newtype Control e r = Control { getControl :: e -> r }

instance Env e (Control e r) where
  env f = Control (getControl =<< f)

instance Res r (Control e r) where
  res = Control . const
  liftRes f = Control (\ e -> let run = (`getControl` e) in run (f run))


inPrd :: Dual e r d => (K r a -> Control e r) -> d s a
inPrd = inD . const

producer :: (Dual e r d, V.Representable v, V.Rep v ~ e) => v a -> d s a
producer v = inPrd (•∘ v)

joinl :: Dual e r d => d e (d a b) -> d a b
joinl p = inD (\ a b -> cont (\ _K -> exD p idV (_K (\ f -> exD f a b))))


inCns :: Dual e r d => (V e a -> Control e r) -> d a r
inCns = inD . fmap const

consumer :: (Dual e r d, K.Representable k, K.Rep k ~ r) => k a -> d a r
consumer k = inCns (k •∘)
