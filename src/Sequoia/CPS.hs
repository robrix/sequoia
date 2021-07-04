{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.CPS
( -- * CPS
  CPS(..)
, inC1
, inC2
, exC1
, exC2
  -- ** Construction
, cps
, liftCPS
, contToCPS
  -- ** Elimination
, cpsToCont
, appCPS
, appCPS2
, pappCPS
, execCPS
, evalCPS
, dnE
  -- ** Currying
, curryCPS
, uncurryCPS
  -- * Delimited continuations
, resetCPS
, shiftCPS
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
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Sequoia.Continuation
import           Sequoia.Disjunction

-- CPS

class (Cat.Category c, Representable k, Profunctor c) => CPS k c | c -> k where
  inC :: (k b -> k a) -> a `c` b
  exC :: a `c` b      -> (k b -> k a)


inC1 :: CPS k c => ((k b1 -> k a1) -> (k b2 -> k a2)) -> (a1 `c` b1 -> a2 `c` b2)
inC1 = dimap exC inC

inC2 :: CPS k c => ((k b1 -> k a1) -> (k b2 -> k a2) -> (k b3 -> k a3)) -> (a1 `c` b1 -> a2 `c` b2 -> a3 `c` b3)
inC2 = dimap2 exC exC inC


exC1 :: CPS k c => (a1 `c` b1 -> a2 `c` b2) -> ((k b1 -> k a1) -> (k b2 -> k a2))
exC1 = dimap inC exC

exC2 :: CPS k c => (a1 `c` b1 -> a2 `c` b2 -> a3 `c` b3) -> ((k b1 -> k a1) -> (k b2 -> k a2) -> (k b3 -> k a3))
exC2 = dimap2 inC inC exC


-- Construction

cps :: CPS k c => (a -> b) -> a `c` b
cps = inC . inK1 . flip (.)

liftCPS :: CPS k c => (a -> k b -> Rep k) -> a `c` b
liftCPS = inC . fmap inK . flip

contToCPS :: CPS k c => (a -> k ••b) -> a `c` b
contToCPS f = liftCPS (exK . runCont . f)


-- Elimination

cpsToCont :: CPS k c => a `c` b -> (a -> k ••b)
cpsToCont c a = Cont (appCPS c a)

appCPS :: CPS k c => a `c` b -> a -> k **b
appCPS c a = inK $ \ k -> exK (exC c k) a

appCPS2 :: CPS k c => a `c` (b `c` d) -> a -> b -> k **d
appCPS2 c = appK2 (exC (rmap exC c))

pappCPS :: CPS k c => a `c` b -> a -> c () b
pappCPS c a = c Cat.<<< inC (•<< const a)

execCPS :: CPS k c => () `c` a -> k **a
execCPS c = appCPS c ()

evalCPS :: CPS k c => i `c` Rep k -> k i
evalCPS c = exC c idK

dnE :: CPS k c => k **c a b -> a `c` b
dnE f = inC (inK . \ k a -> exK f (inK (\ f -> exK (exC f k) a)))


-- Currying

curryCPS :: CPS k c => (a, b) `c` d -> a `c` (b `c` d)
curryCPS c = inC (•<< (`lmap` c) . (,))

uncurryCPS :: CPS k c => a `c` (b `c` d) -> (a, b) `c` d
uncurryCPS c = inC (\ k -> inK ((`exK` k) . uncurry (appCPS2 c)))


-- Delimited continuations

resetCPS :: (CPS j cj, CPS k ck) => ck i (Rep k) -> cj i (Rep k)
resetCPS c = inC (inK . \ k -> exK k . exK (evalCPS c))

shiftCPS :: CPS k c => (k o -> c i (Rep k)) -> c i o
shiftCPS f = inC (evalCPS . f)


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
apCPS f a = inC (inK1 (\ k a' -> exK (exC f (inK (\ f -> exK (exC a (inK (k . f))) a'))) a'))

liftA2CPS :: CPS k c => (x -> y -> z) -> c a x -> c a y -> c a z
liftA2CPS f a b = inC (\ k -> inK (\ a' -> exK (exC a (inK ((`exK` a') . exC b . (k •<<) . f))) a'))


-- Monad

bindCPS :: CPS k c => c a b -> (b -> c a b') -> c a b'
bindCPS m f = inC (inK1 (\ k a -> exK (exC m (inK ((`exK` a) . (`exC` inK k) . f))) a))


-- Arrow

arrCPS :: CPS k c => (a -> b) -> c a b
arrCPS = cps

firstCPS :: CPS k c => c a b -> c (a, d) (b, d)
firstCPS  f = inC (inK . (\ k (l, r) -> exK (appCPS f l) (k •<< (,r))))

secondCPS :: CPS k c => c a b -> c (d, a) (d, b)
secondCPS g = inC (inK . (\ k (l, r) -> exK (appCPS g r) (k •<< (l,))))

splitPrdCPS :: CPS k c => c a b -> c a' b' -> c (a, a') (b, b')
splitPrdCPS f g = inC (inK . (\ k (l, r) -> exK (appCPS f l) (appCPS g r •<< (k •<<) . (,))))

fanoutCPS :: CPS k c => c a b -> c a b' -> c a (b, b')
fanoutCPS = liftA2CPS (,)


-- ArrowChoice

leftCPS :: CPS k c => c a b -> c (Either a d) (Either b d)
leftCPS  f = inC (\ k -> exC f (k •<< inl) <••> (k •<< inr))

rightCPS :: CPS k c => c a b -> c (Either d a) (Either d b)
rightCPS g = inC (\ k -> (k •<< inl) <••> exC g (k •<< inr))

splitSumCPS :: CPS k c => c a1 b1 -> c a2 b2 -> c (Either a1 a2) (Either b1 b2)
splitSumCPS f g = inC (\ k -> exC f (k •<< inl) <••> exC g (k •<< inr))

faninCPS :: CPS k c => c a1 b -> c a2 b -> c (Either a1 a2) b
faninCPS f g = inC ((<••>) <$> exC f <*> exC g)


-- ArrowApply

applyCPS :: CPS k c => c (c a b, a) b
applyCPS = inC (>>- uncurry appCPS)


-- Traversing

wanderCPS :: (CPS k c, Applicative (c ())) => (forall f . Applicative f => (a -> f b) -> (s -> f t)) -> (c a b -> c s t)
wanderCPS traverse c = liftCPS (exK . execCPS . traverse (pappCPS c))


-- Profunctor

dimapCPS :: CPS k c => (a' -> a) -> (b -> b') -> (c a b -> c a' b')
dimapCPS f g = inC . dimap (contramap g) (contramap f) . exC

lmapCPS :: CPS k c => (a' -> a) -> (c a b -> c a' b)
lmapCPS = (`dimapCPS` id)

rmapCPS :: CPS k c => (b -> b') -> (c a b -> c a b')
rmapCPS = (id `dimapCPS`)


-- Deriving

newtype ViaCPS c a b = ViaCPS { runViaCPS :: c a b }
  deriving (CPS k)

instance CPS k c => Cat.Category (ViaCPS c) where
  id = idCPS
  (.) = composeCPS

instance CPS k c => Functor (ViaCPS c a) where
  fmap = fmapCPS

instance CPS k c => Applicative (ViaCPS c a) where
  pure = pureCPS

  liftA2 = liftA2CPS

  (<*>) = apCPS

instance CPS k c => Monad (ViaCPS c a) where
  (>>=) = bindCPS

instance CPS k c => Arrow (ViaCPS c) where
  arr = arrCPS
  first = firstCPS
  second = secondCPS
  (***) = splitPrdCPS
  (&&&) = fanoutCPS

instance CPS k c => ArrowChoice (ViaCPS c) where
  left = leftCPS
  right = rightCPS
  (+++) = splitSumCPS
  (|||) = faninCPS

instance CPS k c => ArrowApply (ViaCPS c) where
  app = applyCPS

instance CPS k c => Strong (ViaCPS c) where
  first' = first
  second' = second

instance CPS k c => Choice (ViaCPS c) where
  left' = left
  right' = right

instance CPS k c => Traversing (ViaCPS c) where
  traverse' = wanderCPS traverse
  wander = wanderCPS

instance CPS k c => Profunctor (ViaCPS c) where
  dimap = dimapCPS

  lmap = lmapCPS

  rmap = rmapCPS
