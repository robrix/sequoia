{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.CPS
( -- * CPS
  CPSFn
, CPS(..)
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

-- CPS

type CPSFn k a b = k b -> k a

class (Cat.Category c, Representable k, Profunctor c) => CPS k c | c -> k where
  inC :: CPSFn k a b -> a `c` b
  exC :: a `c` b     -> CPSFn k a b


_CPS :: (CPS k c, CPS k' c') => Poly (CPSFn k a b) (CPSFn k' a' b') (c a b) (c' a' b')
_CPS = inC <-> exC


inC1 :: CPS k c => (RepFn k b -> RepFn k a) -> a `c` b
inC1 = inC . inK1


(••) :: CPS k c => a `c` b -> CPSFn k a b
(••) = exC

infixl 9 ••


-- Construction

cps :: CPS k c => (a -> b) -> a `c` b
cps = inC1 . flip (.)

liftCPS :: CPS k c => (a -> k b -> Rep k) -> a `c` b
liftCPS = inC . fmap inK . flip


-- Elimination

appC :: CPS k c => a `c` b -> a -> ContFn k b
appC c a k = c •• inK k • a

appC2 :: CPS k c => a `c` (b `c` d) -> a -> b -> ContFn k d
appC2 f a b k = appC f a (\ f -> appC f b k)

appCM :: (CPS k c, MonadK k m) => a `c` b -> (a -> m b)
appCM c a = jump (inK (\ k -> c •• k • a))

appCM2 :: (CPS k c, MonadK k m) => a `c` (b `c` d) -> (a -> b -> m d)
appCM2 c a b = jump (inK (\ k -> c •• inK (\ c -> c •• k • b) • a))

execC :: CPS k c => () `c` a -> k **a
execC c = exC c -<< ()

execCM :: (CPS k c, MonadK k m) => () `c` a -> m a
execCM = jump . execC

evalC :: CPS k c => i `c` Rep k -> k i
evalC = (•• idK)

evalCM :: (CPS k c, MonadK k m) => i `c` Rep k -> (i -> m ())
evalCM c i = jump (inK (const (evalC c • i)))

dnE :: CPS k c => k **(a `c` b) -> a `c` b
dnE f = inC1 (\ k a -> f • inK (\ f -> appC f a k))


-- Currying

curryC :: CPS k c => (a, b) `c` d -> a `c` (b `c` d)
curryC c = inC (•<< (`lmap` c) . (,))

uncurryC :: CPS k c => a `c` (b `c` d) -> (a, b) `c` d
uncurryC c = inC1 (\ k -> ($ k) . uncurry (appC2 c))


-- Delimited continuations

resetC :: (CPS j cj, CPS k ck) => ck i (Rep k) -> cj i (Rep k)
resetC c = inC1 (\ k -> k . (evalC c •))

shiftC :: CPS k c => (k o -> c i (Rep k)) -> c i o
shiftC f = inC (evalC . f)


-- Category

idCPS :: CPS k c => c a a
idCPS = inC id

composeCPS :: CPS k c => c b d -> c a b -> c a d
composeCPS f g = inC (exC g . exC f)


-- Functor

fmapCPS :: CPS k c => (b -> b') -> (c a b -> c a b')
fmapCPS = rmapCPS


-- Applicative

pureCPS :: CPS k c => b -> c a b
pureCPS a = inC (•<< const a)

apCPS :: CPS k c => c a (b -> b') -> (c a b -> c a b')
apCPS f a = inC1 (\ k a' -> f •• inK (\ f -> a •• inK (k . f) • a') • a')

liftA2CPS :: CPS k c => (x -> y -> z) -> c a x -> c a y -> c a z
liftA2CPS f a b = inC1 (\ k a' -> appC a a' (appC b a' . (k .) . f))


-- Monad

bindCPS :: CPS k c => c a b -> (b -> c a b') -> c a b'
bindCPS m f = inC1 (\ k a -> m •• inK ((• a) . (•• inK k) . f) • a)


-- Arrow

arrCPS :: CPS k c => (a -> b) -> c a b
arrCPS = cps

firstCPS :: CPS k c => c a b -> c (a, d) (b, d)
firstCPS  f = inC1 (\ k (l, r) -> appC f l (k . (,r)))

secondCPS :: CPS k c => c a b -> c (d, a) (d, b)
secondCPS g = inC1 (\ k (l, r) -> appC g r (k . (l,)))

splitPrdCPS :: CPS k c => c a b -> c a' b' -> c (a, a') (b, b')
splitPrdCPS f g = inC1 (\ k (l, r) -> appC f l (appC g r . fmap k . (,)))

fanoutCPS :: CPS k c => c a b -> c a b' -> c a (b, b')
fanoutCPS = liftA2CPS (,)


-- ArrowChoice

leftCPS :: CPS k c => c a b -> c (Either a d) (Either b d)
leftCPS  f = inC (\ k -> f •• inlC k <••> inrC k)

rightCPS :: CPS k c => c a b -> c (Either d a) (Either d b)
rightCPS g = inC (\ k -> inlC k <••> g •• inrC k)

splitSumCPS :: CPS k c => c a1 b1 -> c a2 b2 -> c (Either a1 a2) (Either b1 b2)
splitSumCPS f g = inC (\ k -> f •• inlC k <••> g •• inrC k)

faninCPS :: CPS k c => c a1 b -> c a2 b -> c (Either a1 a2) b
faninCPS f g = inC ((<••>) <$> exC f <*> exC g)


-- ArrowApply

applyCPS :: CPS k c => c (c a b, a) b
applyCPS = inC (>>- uncurry (fmap inDN . appC))


-- Traversing

wanderCPS :: (CPS k c, Applicative (c ())) => (forall f . Applicative f => (a -> f b) -> (s -> f t)) -> (c a b -> c s t)
wanderCPS traverse c = liftCPS (exK . execC . traverse (pappC c))
  where
  pappC :: CPS k c => c a b -> a -> c () b
  pappC c a = inC ((a >$) . (c ••))


-- Profunctor

dimapCPS :: CPS k c => (a' -> a) -> (b -> b') -> (c a b -> c a' b')
dimapCPS f g = under (inv _CPS) (dimap (contramap g) (contramap f))

lmapCPS :: CPS k c => (a' -> a) -> (c a b -> c a' b)
lmapCPS = (`dimapCPS` id)

rmapCPS :: CPS k c => (b -> b') -> (c a b -> c a b')
rmapCPS = (id `dimapCPS`)


-- Sieve

sieveCPS :: CPS k c => a `c` b -> (a -> k ••b)
sieveCPS = fmap (Cont . inDN) . appC


-- Representable

tabulateCPS :: CPS k c => (a -> k ••b) -> a `c` b
tabulateCPS f = liftCPS (exK . runCont . f)


-- Deriving

newtype ViaCPS c (k :: Type -> Type) a b = ViaCPS { runViaCPS :: c a b }
  deriving (CPS k)

instance CPS k c => Cat.Category (ViaCPS c k) where
  id = idCPS
  (.) = composeCPS

instance CPS k c => Functor (ViaCPS c k a) where
  fmap = fmapCPS

instance CPS k c => Applicative (ViaCPS c k a) where
  pure = pureCPS

  liftA2 = liftA2CPS

  (<*>) = apCPS

instance CPS k c => Monad (ViaCPS c k a) where
  (>>=) = bindCPS

instance CPS k c => Arrow (ViaCPS c k) where
  arr = arrCPS
  first = firstCPS
  second = secondCPS
  (***) = splitPrdCPS
  (&&&) = fanoutCPS

instance CPS k c => ArrowChoice (ViaCPS c k) where
  left = leftCPS
  right = rightCPS
  (+++) = splitSumCPS
  (|||) = faninCPS

instance CPS k c => ArrowApply (ViaCPS c k) where
  app = applyCPS

instance CPS k c => Strong (ViaCPS c k) where
  first' = first
  second' = second

instance CPS k c => Choice (ViaCPS c k) where
  left' = left
  right' = right

instance CPS k c => Traversing (ViaCPS c k) where
  traverse' = wanderCPS traverse
  wander = wanderCPS

instance CPS k c => Profunctor (ViaCPS c k) where
  dimap = dimapCPS

  lmap = lmapCPS

  rmap = rmapCPS

instance CPS k c => Sieve (ViaCPS c k) ((••) k) where
  sieve = sieveCPS

instance CPS k c => Pro.Representable (ViaCPS c k) where
  type Rep (ViaCPS c k) = (••) k
  tabulate = tabulateCPS
