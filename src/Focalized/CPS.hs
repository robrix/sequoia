module Focalized.CPS
( -- * Continuations
  dnI
, dnE
, liftK
, liftK2
, type (•)(..)
, type (••)
  -- * CPS
, cps
, liftCPS
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
) where

import           Control.Arrow
import qualified Control.Category as Cat
import           Control.Monad (ap)
import           Control.Monad.Trans.Class
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Focalized.Disjunction

-- Continuations

dnI :: a -> r ••a
dnI = K . flip runK

dnE :: r ••CPS r a b -> CPS r a b
dnE f = CPS (\ k a -> runK f (K (\ f -> runCPS f k a)))

liftK :: ((a -> r) -> (b -> r)) -> (r •a -> r •b)
liftK f (K a) = K (f a)

liftK2 :: ((a -> r) -> (b -> r) -> (c -> r)) -> (r •a -> r •b -> r •c)
liftK2 f (K a) (K b) = K (f a b)

newtype r •a = K { runK :: a -> r }

instance Cat.Category (•) where
  id = K id
  K f . K g = K (g . f)

instance Contravariant ((•) r) where
  contramap f = K . (. f) . runK


type r ••a = r •r •a

infixr 9 •, ••


-- CPS

cps :: (a -> b) -> CPS r a b
cps = CPS . flip (.)

liftCPS :: (a -> (b -> r) -> r) -> CPS r a b
liftCPS = CPS . flip

appCPS :: CPS r a b -> a -> (b -> r) -> r
appCPS c a k = runCPS c k a

appCPS2 :: CPS r a (CPS r b c) -> a -> b -> (c -> r) -> r
appCPS2 c a b = appCPS c a . flip (`appCPS` b)

pappCPS :: CPS r a b -> a -> CPS r () b
pappCPS c a = c Cat.<<< pure a

execCPS :: CPS r () a -> (a -> r) -> r
execCPS c = appCPS c ()

evalCPS :: CPS r i r -> i -> r
evalCPS c = runCPS c id

refoldCPS :: Traversable f => CPS r (f b) b -> CPS r a (f a) -> CPS r a b
refoldCPS f g = go where go = f Cat.<<< traverse' go Cat.<<< g

resetCPS :: CPS o i o -> CPS r i o
resetCPS c = CPS (. evalCPS c)

shiftCPS :: ((o -> r) -> CPS r i r) -> CPS r i o
shiftCPS f = CPS (evalCPS . f)

curryCPS :: CPS r (a, b) c -> CPS r a (CPS r b c)
curryCPS c = CPS (\ k -> k . (`lmap` c) . (,))

uncurryCPS :: CPS r a (CPS r b c) -> CPS r (a, b) c
uncurryCPS c = CPS (\ k -> uncurry (flip (runCPS c . flip (`runCPS` k))))

newtype CPS r a b = CPS { runCPS :: (b -> r) -> (a -> r) }

instance Cat.Category (CPS r) where
  id = CPS id
  CPS f . CPS g = CPS (g . f)

instance Functor (CPS r a) where
  fmap f (CPS r) = CPS (r . (. f))

instance Applicative (CPS r a) where
  pure a = CPS (const . ($ a))
  (<*>) = ap

instance Monad (CPS r a) where
  r >>= f = CPS $ \ k a -> runCPS r (\ a' -> runCPS (f a') k a) a

instance Arrow (CPS r) where
  arr = cps
  first  f = CPS (\ k (l, r) -> appCPS f l (k . (, r)))
  second g = CPS (\ k (l, r) -> appCPS g r (k . (l,)))
  f *** g = CPS (\ k (l, r) -> appCPS f l (appCPS g r . fmap k . (,)))
  f &&& g = CPS (\ k a -> appCPS f a (appCPS g a . fmap k . (,)))

instance ArrowChoice (CPS r) where
  left  f = CPS (\ k -> runCPS f (k . inl) <--> k . inr)
  right g = CPS (\ k -> k . inl <--> runCPS g (k . inr))
  f +++ g = CPS (\ k -> runCPS f (k . inl) <--> runCPS g (k . inr))
  f ||| g = CPS ((<-->) <$> runCPS f <*> runCPS g)

instance ArrowApply (CPS r) where
  app = CPS (flip (uncurry appCPS))

instance Profunctor (CPS r) where
  dimap f g (CPS c) = CPS ((. f) . c . (. g))

instance Strong (CPS r) where
  first' = first
  second' = second

instance Choice (CPS r) where
  left' = left
  right' = right

instance Traversing (CPS r) where
  traverse' c = liftCPS (execCPS . traverse (pappCPS c))
  wander traverse c = liftCPS (execCPS . traverse (pappCPS c))


newtype CPST r a m b = CPST { runCPST :: CPS (m r) a b }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (CPST r i) where
  lift m = CPST (CPS (const . (m >>=)))
