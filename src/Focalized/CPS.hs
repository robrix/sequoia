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
  -- * Cont
, Cont(..)
) where

import           Control.Applicative (liftA2)
import           Control.Arrow
import qualified Control.Category as Cat
import           Control.Monad (ap)
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Focalized.Continuation
import           Focalized.Disjunction

-- CPS

cps :: Continuation k => (a -> b) -> CPS k a b
cps = CPS . inK1 . flip (.)

liftCPS :: Continuation k => (a -> k b -> R k) -> CPS k a b
liftCPS = CPS . fmap inK . flip

contToCPS :: Continuation  k => (a -> Cont k b) -> CPS k a b
contToCPS f = liftCPS (exK . runCont . f)

cpsToCont :: Continuation k => CPS k a b -> (a -> Cont k b)
cpsToCont c a = Cont (appCPS c a)

appCPS :: Continuation k => CPS k a b -> a -> k (k b)
appCPS c a = inK $ \ k -> exK (runCPS c k) a

appCPS2 :: Continuation k => CPS k a (CPS k b c) -> a -> b -> k (k c)
appCPS2 c = appK2 (runCPS (runCPS <$> c))

pappCPS :: Continuation k => CPS k a b -> a -> CPS k () b
pappCPS c a = c Cat.<<< pure a

execCPS :: Continuation k => CPS k () a -> k (k a)
execCPS c = appCPS c ()

evalCPS :: Continuation k => CPS k i (R k) -> k i
evalCPS c = runCPS c idK

refoldCPS :: (Continuation k, Traversable f) => CPS k (f b) b -> CPS k a (f a) -> CPS k a b
refoldCPS f g = go where go = f Cat.<<< traverse' go Cat.<<< g

resetCPS :: (Continuation j, Continuation k) => CPS k i (R k) -> CPS j i (R k)
resetCPS c = CPS (inK . \ k -> exK k . exK (evalCPS c))

shiftCPS :: Continuation k => (k o -> CPS k i (R k)) -> CPS k i o
shiftCPS f = CPS (evalCPS . f)

curryCPS :: Continuation k => CPS k (a, b) c -> CPS k a (CPS k b c)
curryCPS c = CPS (•<< (`lmap` c) . (,))

uncurryCPS :: Continuation k => CPS k a (CPS k b c) -> CPS k (a, b) c
uncurryCPS c = CPS (\ k -> inK ((`exK` k) . uncurry (appCPS2 c)))

newtype CPS k a b = CPS { runCPS :: k b -> k a }

instance Cat.Category (CPS k) where
  id = CPS id
  CPS f . CPS g = CPS (g . f)

instance Contravariant k => Functor (CPS k a) where
  fmap f (CPS r) = CPS (r . contramap f)

instance Continuation k => Applicative (CPS k a) where
  pure a = CPS (inK . const . (`exK` a))
  (<*>) = ap

instance Continuation k => Monad (CPS k a) where
  r >>= f = CPS $ inK . \ k a -> exK (runCPS r (inK (\ a' -> exK (runCPS (f a') k) a))) a

instance Continuation k => Arrow (CPS k) where
  arr = cps
  first  f = CPS (inK . (\ k (l, r) -> exK (appCPS f l) (k •<< (,r))))
  second g = CPS (inK . (\ k (l, r) -> exK (appCPS g r) (k •<< (l,))))
  f *** g  = CPS (inK . (\ k (l, r) -> exK (appCPS f l) (appCPS g r •<< (k •<<) . (,))))
  (&&&) = liftA2 (,)

instance Continuation k => ArrowChoice (CPS k) where
  left  f = CPS (\ k -> runCPS f (k •<< inl) <••> (k •<< inr))
  right g = CPS (\ k -> (k •<< inl) <••> runCPS g (k •<< inr))
  f +++ g = CPS (\ k -> runCPS f (k •<< inl) <••> runCPS g (k •<< inr))
  f ||| g = CPS ((<••>) <$> runCPS f <*> runCPS g)

instance Continuation k => ArrowApply (CPS k) where
  app = CPS (>>- uncurry appCPS)

instance Contravariant k => Profunctor (CPS k) where
  dimap f g (CPS c) = CPS (dimap (contramap g) (contramap f) c)

instance Continuation k => Strong (CPS k) where
  first' = first
  second' = second

instance Continuation k => Choice (CPS k) where
  left' = left
  right' = right

instance Continuation k => Traversing (CPS k) where
  traverse' c = liftCPS (exK . execCPS . traverse (pappCPS c))
  wander traverse c = liftCPS (exK . execCPS . traverse (pappCPS c))


dnE :: Continuation k => R k ••CPS k a b -> CPS k a b
dnE f = CPS (inK . \ k a -> f • inK (\ f -> exK (runCPS f k) a))
