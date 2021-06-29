module Focalized.CPS
( -- * Continuations
  liftK
, lowerK
, liftK2
, type (•)(..)
, type (••)
  -- * Double negation
, liftDN
, lowerDN
, dnI
, dnE
  -- * CPS
, cps
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
, CPST(..)
  -- * Cont
, Cont(..)
) where

import           Control.Applicative (liftA2)
import           Control.Arrow
import qualified Control.Category as Cat
import           Control.Monad (ap)
import           Control.Monad.Trans.Class
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Focalized.Disjunction

-- Continuations

liftK :: ((a -> r) -> (b -> r)) -> (r •a -> r •b)
liftK = dimap (•) K

lowerK :: (r •a -> r •b) -> ((a -> r) -> (b -> r))
lowerK = dimap K (•)

liftK2 :: ((a -> r) -> (b -> r) -> (c -> r)) -> (r •a -> r •b -> r •c)
liftK2 f (K a) (K b) = K (f a b)

newtype r •a = K { (•) :: a -> r }

instance Cat.Category (•) where
  id = K id
  K f . K g = K (g . f)

instance Contravariant ((•) r) where
  contramap f = K . (. f) . (•)


-- Double negation

type r ••a = r •r •a

infixr 9 •, ••


dnI :: a -> r ••a
dnI = K . flip (•)

dnE :: r ••CPS r a b -> CPS r a b
dnE f = CPS (\ k -> K (\ a -> f • K (\ f -> runCPS f k • a)))

liftDN :: ((a -> r) -> r) -> r ••a
liftDN = K . lmap (•)

lowerDN :: r ••a -> (a -> r) -> r
lowerDN = lmap K . (•)


-- CPS

cps :: (a -> b) -> CPS r a b
cps = CPS . liftK . flip (.)

liftCPS :: (a -> r •b -> r) -> CPS r a b
liftCPS = CPS . fmap K . flip

contToCPS :: (a -> Cont r b) -> CPS r a b
contToCPS f = liftCPS ((•) . runCont . f)

cpsToCont :: CPS r a b -> (a -> Cont r b)
cpsToCont c a = Cont (appCPS c a)

appCPS :: CPS r a b -> a -> r ••b
appCPS c a = K $ \ k -> runCPS c k • a

appCPS2 :: CPS r a (CPS r b c) -> a -> b -> r ••c
appCPS2 c a b = appCPS c a Cat.>>> K (\ k -> K (\ c -> appCPS c b • k))

pappCPS :: CPS r a b -> a -> CPS r () b
pappCPS c a = c Cat.<<< pure a

execCPS :: CPS r () a -> r ••a
execCPS c = appCPS c ()

evalCPS :: CPS r i r -> r •i
evalCPS c = runCPS c Cat.id

refoldCPS :: Traversable f => CPS r (f b) b -> CPS r a (f a) -> CPS r a b
refoldCPS f g = go where go = f Cat.<<< traverse' go Cat.<<< g

resetCPS :: CPS o i o -> CPS r i o
resetCPS c = CPS (Cat.>>> evalCPS c)

shiftCPS :: (r •o -> CPS r i r) -> CPS r i o
shiftCPS f = CPS (evalCPS . f)

curryCPS :: CPS r (a, b) c -> CPS r a (CPS r b c)
curryCPS c = CPS ((`lmap` c) . (,) >$<)

uncurryCPS :: CPS r a (CPS r b c) -> CPS r (a, b) c
uncurryCPS c = CPS (\ k -> K ((• k) . uncurry (appCPS2 c)))

newtype CPS r a b = CPS { runCPS :: r •b -> r •a }

instance Cat.Category (CPS r) where
  id = CPS id
  CPS f . CPS g = CPS (g . f)

instance Functor (CPS r a) where
  fmap f (CPS r) = CPS (r . contramap f)

instance Applicative (CPS r a) where
  pure a = CPS (K . const . (• a))
  (<*>) = ap

instance Monad (CPS r a) where
  r >>= f = CPS $ \ k -> K $ \ a -> runCPS r (K (\ a' -> runCPS (f a') k • a)) • a

instance Arrow (CPS r) where
  arr = cps
  first  f = CPS (K . (\ k (l, r) -> appCPS f l • ((,r) >$< k)))
  second g = CPS (K . (\ k (l, r) -> appCPS g r • ((l,) >$< k)))
  f *** g = CPS (K . (\ k (l, r) -> appCPS f l • ((>$< k) . (,) >$< appCPS g r)))
  (&&&) = liftA2 (,)

instance ArrowChoice (CPS r) where
  left  f = CPS (\ k -> runCPS f (inl >$< k) <••> (inr >$< k))
  right g = CPS (\ k -> inl >$< k <••> runCPS g (inr >$< k))
  f +++ g = CPS (\ k -> runCPS f (inl >$< k) <••> runCPS g (inr >$< k))
  f ||| g = CPS ((<••>) <$> runCPS f <*> runCPS g)

(<••>) :: Disj d => c •a -> c •b -> c •(a `d` b)
f <••> g = K $ (f •) <--> (g •)

infix 3 <••>

instance ArrowApply (CPS r) where
  app = CPS $ K . \ k -> (• k) . uncurry appCPS

instance Profunctor (CPS r) where
  dimap f g (CPS c) = CPS (dimap (contramap g) (contramap f) c)

instance Strong (CPS r) where
  first' = first
  second' = second

instance Choice (CPS r) where
  left' = left
  right' = right

instance Traversing (CPS r) where
  traverse' c = liftCPS ((•) . execCPS . traverse (pappCPS c))
  wander traverse c = liftCPS ((•) . execCPS . traverse (pappCPS c))


newtype CPST r a m b = CPST { runCPST :: CPS (m r) a b }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (CPST r i) where
  lift m = CPST (CPS (liftK (const . (m >>=))))


newtype Cont r a = Cont { runCont :: r ••a }

instance Functor (Cont r) where
  fmap f = Cont . contramap (contramap f) . runCont

instance Applicative (Cont r) where
  pure = Cont . K . flip (•)
  (<*>) = ap

instance Monad (Cont r) where
  Cont m >>= f = Cont (K (\ k -> m • K (\ a -> runCont (f a) • k)))
