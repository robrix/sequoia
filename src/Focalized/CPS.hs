{-# LANGUAGE QuantifiedConstraints #-}
module Focalized.CPS
( -- * CPS
  cps
, liftCPS
, contToCPS
, cpsToCont
, appCPS
, appCPS2
, pappCPS
, execCPS
, evalCPS
, refoldCPS
, resetCPS
, shiftCPS
, curryCPS
, uncurryCPS
, CPS(..)
, dnE
  -- * CPS abstraction
, CPS'(..)
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
  -- ** Deriving
, ViaCPS(..)
) where

import           Control.Applicative (liftA2)
import           Control.Arrow
import qualified Control.Category as Cat
import           Data.Functor.Contravariant
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Focalized.Continuation
import           Focalized.Disjunction

-- CPS

cps :: (Continuation k, CPS' c) => (a -> b) -> c k a b
cps = inC . inK1 . flip (.)

liftCPS :: (Continuation k, CPS' c) => (a -> k b -> R k) -> c k a b
liftCPS = inC . fmap inK . flip

contToCPS :: (Continuation k, CPS' c) => (a -> Cont k b) -> c k a b
contToCPS f = liftCPS (exK . runCont . f)

cpsToCont :: (Continuation k, CPS' c) => c k a b -> (a -> Cont k b)
cpsToCont c a = Cont (appCPS c a)

appCPS :: (Continuation k, CPS' c) => c k a b -> a -> k (k b)
appCPS c a = inK $ \ k -> exK (exC c k) a

appCPS2 :: (Continuation k, CPS' c) => c k a (c k b d) -> a -> b -> k (k d)
appCPS2 c = appK2 (exC (rmap exC c))

pappCPS :: (Continuation k, CPS' c) => c k a b -> a -> c k () b
pappCPS c a = c Cat.<<< inC (•<< const a)

execCPS :: (Continuation k, CPS' c) => c k () a -> k (k a)
execCPS c = appCPS c ()

evalCPS :: (Continuation k, CPS' c) => c k i (R k) -> k i
evalCPS c = exC c idK

refoldCPS :: (Cat.Category c, Traversing c, Traversable f) => f b `c` b -> a `c` f a -> a `c` b
refoldCPS f g = go where go = f Cat.<<< traverse' go Cat.<<< g

resetCPS :: (CPS' c, Continuation j, Continuation k) => c k i (R k) -> c j i (R k)
resetCPS c = inC (inK . \ k -> exK k . exK (evalCPS c))

shiftCPS :: (Continuation k, CPS' c) => (k o -> c k i (R k)) -> c k i o
shiftCPS f = inC (evalCPS . f)

curryCPS :: (Continuation k, CPS' c) => c k (a, b) d -> c k a (c k b d)
curryCPS c = inC (•<< (`lmap` c) . (,))

uncurryCPS :: (Continuation k, CPS' c) => c k a (c k b d) -> c k (a, b) d
uncurryCPS c = inC (\ k -> inK ((`exK` k) . uncurry (appCPS2 c)))

newtype CPS k a b = CPS { runCPS :: k b -> k a }
  deriving (Arrow, ArrowChoice, Cat.Category, Choice, Profunctor, Strong, Traversing) via (ViaCPS CPS k)
  deriving (Applicative, Functor, Monad) via (ViaCPS CPS k a)

instance Continuation k => ArrowApply (CPS k) where
  app = applyCPS


dnE :: Continuation k => k (k (CPS k a b)) -> CPS k a b
dnE f = CPS (inK . \ k a -> exK f (inK (\ f -> exK (runCPS f k) a)))


-- CPS abstraction

class (forall k . Cat.Category (c k), forall k . Contravariant k => Profunctor (c k)) => CPS' c where
  inC :: (k b -> k a) -> c k a b
  exC :: c k a b      -> (k b -> k a)

instance CPS' CPS where
  inC = CPS
  exC = runCPS


-- Category

idCPS :: CPS' c => c k a a
idCPS = inC id

composeCPS :: CPS' c => c k b d -> c k a b -> c k a d
composeCPS f g = inC (exC g . exC f)


-- Functor

fmapCPS :: (Contravariant k, CPS' c) => (b -> b') -> (c k a b -> c k a b')
fmapCPS = rmapCPS


-- Applicative

pureCPS :: (Continuation k, CPS' c) => b -> c k a b
pureCPS a = inC (•<< const a)

apCPS :: (Continuation k, CPS' c) => c k a (b -> b') -> (c k a b -> c k a b')
apCPS f a = inC (inK1 (\ k a' -> exK (exC f (inK (\ f -> exK (exC a (inK (k . f))) a'))) a'))

liftA2CPS :: (Continuation k, CPS' c) => (x -> y -> z) -> c k a x -> c k a y -> c k a z
liftA2CPS f a b = inC (\ k -> inK (\ a' -> exK (exC a (inK ((`exK` a') . exC b . (k •<<) . f))) a'))


-- Monad

bindCPS :: (Continuation k, CPS' c) => c k a b -> (b -> c k a b') -> c k a b'
bindCPS m f = inC (inK1 (\ k a -> exK (exC m (inK ((`exK` a) . (`exC` inK k) . f))) a))


-- Arrow

arrCPS :: (Continuation k, CPS' c) => (a -> b) -> c k a b
arrCPS = cps

firstCPS :: (Continuation k, CPS' c) => c k a b -> c k (a, d) (b, d)
firstCPS  f = inC (inK . (\ k (l, r) -> exK (appCPS f l) (k •<< (,r))))

secondCPS :: (Continuation k, CPS' c) => c k a b -> c k (d, a) (d, b)
secondCPS g = inC (inK . (\ k (l, r) -> exK (appCPS g r) (k •<< (l,))))

splitPrdCPS :: (Continuation k, CPS' c) => c k a b -> c k a' b' -> c k (a, a') (b, b')
splitPrdCPS f g = inC (inK . (\ k (l, r) -> exK (appCPS f l) (appCPS g r •<< (k •<<) . (,))))

fanoutCPS :: (Continuation k, CPS' c) => c k a b -> c k a b' -> c k a (b, b')
fanoutCPS = liftA2CPS (,)


-- ArrowChoice

leftCPS :: (Continuation k, CPS' c) => c k a b -> c k (Either a d) (Either b d)
leftCPS  f = inC (\ k -> exC f (k •<< inl) <••> (k •<< inr))

rightCPS :: (Continuation k, CPS' c) => c k a b -> c k (Either d a) (Either d b)
rightCPS g = inC (\ k -> (k •<< inl) <••> exC g (k •<< inr))

splitSumCPS :: (Continuation k, CPS' c) => c k a1 b1 -> c k a2 b2 -> c k (Either a1 a2) (Either b1 b2)
splitSumCPS f g = inC (\ k -> exC f (k •<< inl) <••> exC g (k •<< inr))

faninCPS :: (Continuation k, CPS' c) => c k a1 b -> c k a2 b -> c k (Either a1 a2) b
faninCPS f g = inC ((<••>) <$> exC f <*> exC g)


-- ArrowApply

applyCPS :: (Continuation k, CPS' c) => c k (c k a b, a) b
applyCPS = inC (>>- uncurry appCPS)


-- Traversing

wanderCPS :: (Continuation k, CPS' c, Applicative (c k ())) => (forall f . Applicative f => (a -> f b) -> (s -> f t)) -> c k a b -> c k s t
wanderCPS traverse c = liftCPS (exK . execCPS . traverse (pappCPS c))


-- Profunctor

dimapCPS :: (Contravariant k, CPS' c) => (a' -> a) -> (b -> b') -> (c k a b -> c k a' b')
dimapCPS f g = inC . dimap (contramap g) (contramap f) . exC

lmapCPS :: (Contravariant k, CPS' c) => (a' -> a) -> (c k a b -> c k a' b)
lmapCPS = (`dimapCPS` id)

rmapCPS :: (Contravariant k, CPS' c) => (b -> b') -> (c k a b -> c k a b')
rmapCPS = (id `dimapCPS`)


-- Deriving

newtype ViaCPS c (k :: Type -> Type) a b = ViaCPS { runViaCPS :: c k a b }
  deriving (CPS')

instance CPS' c => Cat.Category (ViaCPS c k) where
  id = idCPS
  (.) = composeCPS

instance (Contravariant k, CPS' c) => Functor (ViaCPS c k a) where
  fmap = fmapCPS

instance (Continuation k, CPS' c) => Applicative (ViaCPS c k a) where
  pure = pureCPS

  liftA2 = liftA2CPS

  (<*>) = apCPS

instance (Continuation k, CPS' c) => Monad (ViaCPS c k a) where
  (>>=) = bindCPS

instance (Continuation k, CPS' c) => Arrow (ViaCPS c k) where
  arr = arrCPS
  first = firstCPS
  second = secondCPS
  (***) = splitPrdCPS
  (&&&) = fanoutCPS

instance (Continuation k, CPS' c) => ArrowChoice (ViaCPS c k) where
  left = leftCPS
  right = rightCPS
  (+++) = splitSumCPS
  (|||) = faninCPS

instance (Continuation k, CPS' c) => ArrowApply (ViaCPS c k) where
  app = applyCPS

instance (Continuation k, CPS' c) => Strong (ViaCPS c k) where
  first' = first
  second' = second

instance (Continuation k, CPS' c) => Choice (ViaCPS c k) where
  left' = left
  right' = right

instance (Continuation k, CPS' c) => Traversing (ViaCPS c k) where
  traverse' = wanderCPS traverse
  wander = wanderCPS

instance (Contravariant k, CPS' c) => Profunctor (ViaCPS c k) where
  dimap = dimapCPS

  lmap = lmapCPS

  rmap = rmapCPS
