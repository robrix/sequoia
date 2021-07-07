{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.CPS
( -- * ContPassing
  CFn
, ContPassing(..)
, _CPS
, inC1
, (••)
  -- ** Construction
, cps
, liftCPS
  -- ** Elimination
, appC
, appC2
, appCM
, appCM2
, execC
, execCM
, evalC
, evalCM
, dnE
  -- ** Currying
, curryC
, uncurryC
  -- * Delimited continuations
, resetC
, shiftC
  -- ** Category
, idCPS
, composeCPS
  -- ** Functor
, fmapCPS
  -- ** Applicative
, pureCPS
, apCPS
, liftA2CPS
  -- ** Monad
, bindCPS
  -- ** Arrow
, arrCPS
, firstCPS
, secondCPS
, splitPrdCPS
, fanoutCPS
  -- ** ArrowChoice
, leftCPS
, rightCPS
, splitSumCPS
, faninCPS
  -- ** ArrowApply
, applyCPS
  -- ** Traversing
, wanderCPS
  -- ** Profunctor
, dimapCPS
, lmapCPS
, rmapCPS
  -- ** Sieve
, sieveCPS
  -- ** Representable
, tabulateCPS
  -- ** Deriving
, ViaCPS(..)
) where

import           Control.Applicative (liftA2)
import           Control.Arrow
import qualified Control.Category as Cat
import           Data.Functor.Contravariant
import           Data.Kind (Type)
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve
import           Data.Profunctor.Traversing
import           Sequoia.Bijection
import           Sequoia.Continuation
import           Sequoia.Disjunction

-- ContPassing

type CFn k a b = k b -> k a

class (Cat.Category c, Continuation k, Profunctor c) => ContPassing k c | c -> k where
  inC :: CFn k a b -> a `c` b
  exC :: a `c` b     -> CFn k a b


_CPS :: (ContPassing k c, ContPassing k' c') => Optic Iso (c a b) (c' a' b') (CFn k a b) (CFn k' a' b')
_CPS = exC <-> inC


inC1 :: ContPassing k c => (KFn k b -> KFn k a) -> a `c` b
inC1 = inC . inK1


(••) :: ContPassing k c => a `c` b -> CFn k a b
(••) = exC

infixl 9 ••


-- Construction

cps :: ContPassing k c => (a -> b) -> a `c` b
cps = inC1 . flip (.)

liftCPS :: ContPassing k c => (a -> k b -> KRep k) -> a `c` b
liftCPS = inC . fmap inK . flip


-- Elimination

appC :: ContPassing k c => a `c` b -> a -> ContFn k b
appC c a k = c •• inK k • a

appC2 :: ContPassing k c => a `c` (b `c` d) -> a -> b -> ContFn k d
appC2 f a b k = appC f a (\ f -> appC f b k)

appCM :: (ContPassing k c, MonadK k m) => a `c` b -> (a -> m b)
appCM c a = jump (inK (\ k -> c •• k • a))

appCM2 :: (ContPassing k c, MonadK k m) => a `c` (b `c` d) -> (a -> b -> m d)
appCM2 c a b = jump (inK (\ k -> c •• inK (\ c -> c •• k • b) • a))

execC :: ContPassing k c => () `c` a -> k **a
execC c = exC c -<< ()

execCM :: (ContPassing k c, MonadK k m) => () `c` a -> m a
execCM = jump . execC

evalC :: ContPassing k c => i `c` KRep k -> k i
evalC = (•• idK)

evalCM :: (ContPassing k c, MonadK k m) => i `c` KRep k -> (i -> m ())
evalCM c i = jump (inK (const (evalC c • i)))

dnE :: ContPassing k c => k **(a `c` b) -> a `c` b
dnE f = inC1 (\ k a -> f • inK (\ f -> appC f a k))


-- Currying

curryC :: ContPassing k c => (a, b) `c` d -> a `c` (b `c` d)
curryC c = inC (•<< (`lmap` c) . (,))

uncurryC :: ContPassing k c => a `c` (b `c` d) -> (a, b) `c` d
uncurryC c = inC1 (\ k -> ($ k) . uncurry (appC2 c))


-- Delimited continuations

resetC :: (ContPassing j cj, ContPassing k ck) => ck i (KRep k) -> cj i (KRep k)
resetC c = inC1 (\ k -> k . (evalC c •))

shiftC :: ContPassing k c => (k o -> c i (KRep k)) -> c i o
shiftC f = inC (evalC . f)


-- Category

idCPS :: ContPassing k c => c a a
idCPS = inC id

composeCPS :: ContPassing k c => c b d -> c a b -> c a d
composeCPS f g = inC (exC g . exC f)


-- Functor

fmapCPS :: ContPassing k c => (b -> b') -> (c a b -> c a b')
fmapCPS = rmapCPS


-- Applicative

pureCPS :: ContPassing k c => b -> c a b
pureCPS a = inC (•<< const a)

apCPS :: ContPassing k c => c a (b -> b') -> (c a b -> c a b')
apCPS f a = inC1 (\ k a' -> f •• inK (\ f -> a •• inK (k . f) • a') • a')

liftA2CPS :: ContPassing k c => (x -> y -> z) -> c a x -> c a y -> c a z
liftA2CPS f a b = inC1 (\ k a' -> appC a a' (appC b a' . (k .) . f))


-- Monad

bindCPS :: ContPassing k c => c a b -> (b -> c a b') -> c a b'
bindCPS m f = inC1 (\ k a -> m •• inK ((• a) . (•• inK k) . f) • a)


-- Arrow

arrCPS :: ContPassing k c => (a -> b) -> c a b
arrCPS = cps

firstCPS :: ContPassing k c => c a b -> c (a, d) (b, d)
firstCPS  f = inC1 (\ k (l, r) -> appC f l (k . (,r)))

secondCPS :: ContPassing k c => c a b -> c (d, a) (d, b)
secondCPS g = inC1 (\ k (l, r) -> appC g r (k . (l,)))

splitPrdCPS :: ContPassing k c => c a b -> c a' b' -> c (a, a') (b, b')
splitPrdCPS f g = inC1 (\ k (l, r) -> appC f l (appC g r . fmap k . (,)))

fanoutCPS :: ContPassing k c => c a b -> c a b' -> c a (b, b')
fanoutCPS = liftA2CPS (,)


-- ArrowChoice

leftCPS :: ContPassing k c => c a b -> c (Either a d) (Either b d)
leftCPS  f = inC (\ k -> f •• inlC k <••> inrC k)

rightCPS :: ContPassing k c => c a b -> c (Either d a) (Either d b)
rightCPS g = inC (\ k -> inlC k <••> g •• inrC k)

splitSumCPS :: ContPassing k c => c a1 b1 -> c a2 b2 -> c (Either a1 a2) (Either b1 b2)
splitSumCPS f g = inC (\ k -> f •• inlC k <••> g •• inrC k)

faninCPS :: ContPassing k c => c a1 b -> c a2 b -> c (Either a1 a2) b
faninCPS f g = inC ((<••>) <$> exC f <*> exC g)


-- ArrowApply

applyCPS :: ContPassing k c => c (c a b, a) b
applyCPS = inC (>>- uncurry (fmap inDN . appC))


-- Traversing

wanderCPS :: (ContPassing k c, Applicative (c ())) => (forall f . Applicative f => (a -> f b) -> (s -> f t)) -> (c a b -> c s t)
wanderCPS traverse c = liftCPS (exK . execC . traverse (pappC c))
  where
  pappC :: ContPassing k c => c a b -> a -> c () b
  pappC c a = inC ((a >$) . (c ••))


-- Profunctor

dimapCPS :: ContPassing k c => (a' -> a) -> (b -> b') -> (c a b -> c a' b')
dimapCPS f g = under _CPS (dimap (contramap g) (contramap f))

lmapCPS :: ContPassing k c => (a' -> a) -> (c a b -> c a' b)
lmapCPS = (`dimapCPS` id)

rmapCPS :: ContPassing k c => (b -> b') -> (c a b -> c a b')
rmapCPS = (id `dimapCPS`)


-- Sieve

sieveCPS :: ContPassing k c => a `c` b -> (a -> k ••b)
sieveCPS = fmap (Cont . inDN) . appC


-- Representable

tabulateCPS :: ContPassing k c => (a -> k ••b) -> a `c` b
tabulateCPS f = liftCPS (exK . runCont . f)


-- Deriving

newtype ViaCPS c (k :: Type -> Type) a b = ViaCPS { runViaCPS :: c a b }
  deriving (ContPassing k)

instance ContPassing k c => Cat.Category (ViaCPS c k) where
  id = idCPS
  (.) = composeCPS

instance ContPassing k c => Functor (ViaCPS c k a) where
  fmap = fmapCPS

instance ContPassing k c => Applicative (ViaCPS c k a) where
  pure = pureCPS

  liftA2 = liftA2CPS

  (<*>) = apCPS

instance ContPassing k c => Monad (ViaCPS c k a) where
  (>>=) = bindCPS

instance ContPassing k c => Arrow (ViaCPS c k) where
  arr = arrCPS
  first = firstCPS
  second = secondCPS
  (***) = splitPrdCPS
  (&&&) = fanoutCPS

instance ContPassing k c => ArrowChoice (ViaCPS c k) where
  left = leftCPS
  right = rightCPS
  (+++) = splitSumCPS
  (|||) = faninCPS

instance ContPassing k c => ArrowApply (ViaCPS c k) where
  app = applyCPS

instance ContPassing k c => Strong (ViaCPS c k) where
  first' = first
  second' = second

instance ContPassing k c => Choice (ViaCPS c k) where
  left' = left
  right' = right

instance ContPassing k c => Traversing (ViaCPS c k) where
  traverse' = wanderCPS traverse
  wander = wanderCPS

instance ContPassing k c => Profunctor (ViaCPS c k) where
  dimap = dimapCPS

  lmap = lmapCPS

  rmap = rmapCPS

instance ContPassing k c => Sieve (ViaCPS c k) ((••) k) where
  sieve = sieveCPS

instance ContPassing k c => Pro.Representable (ViaCPS c k) where
  type Rep (ViaCPS c k) = (••) k
  tabulate = tabulateCPS
