{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.EPS
( -- * EPS
  EnvPassing(..)
, _E
, inE1
, inE1'
, exE1
  -- ** Construction
, eps
, liftE
  -- ** Elimination
, appE
, appE2
, (↑)
, (<↑)
  -- ** Currying
, curryE
, uncurryE
  -- ** Category
, idE
, composeE
  -- ** Functor
, fmapE
  -- ** Distributive
, distributeE
, collectE
  -- ** Representable
, tabulateE
, indexE
  -- ** Applicative
, pureE
, apE
, liftA2E
  -- ** Monad
, bindE
  -- ** Comonad
, extractE
, extendE
, duplicateE
  -- ** Profunctor
, dimapE
, lmapE
, rmapE
  -- ** Cochoice
, unleftE
, unrightE
  -- ** Costrong
, unfirstE
, unsecondE
  -- ** Cosieve
, cosieveE
  -- ** Corepresentable
, cotabulateE
  -- * Concrete
, E(..)
) where

import           Control.Applicative (liftA2)
import qualified Control.Category as Cat
import           Control.Comonad
import           Control.Comonad.Store
import           Data.Distributive
import           Data.Functor.Rep
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve
import           Sequoia.Bijection
import           Sequoia.Conjunction
import           Sequoia.Disjunction
import           Sequoia.Value

-- EPS

class (Cat.Category e, Representable v, Profunctor e) => EnvPassing v e | e -> v where
  inE :: (v a -> v b) -> a `e` b
  exE :: a `e` b    -> (v a -> v b)


_E :: (EnvPassing v e, EnvPassing v' e') => Optic Iso (e a b) (e' a' b') (v a -> v b) (v' a' -> v' b')
_E = exE <-> inE


inE1 :: EnvPassing v e => ((Rep v -> a) -> (Rep v -> b)) -> a `e` b
inE1 = inE . inV1

inE1' :: EnvPassing v e => (v a -> (Rep v -> b)) -> a `e` b
inE1' = inE . inV1'

exE1 :: EnvPassing v e => a `e` b -> ((Rep v -> a) -> (Rep v -> b))
exE1 = exV1 . exE


-- Construction

eps :: EnvPassing v e => (a -> b) -> a `e` b
eps = inE1 . (.)

liftE :: EnvPassing v e => (Rep v -> ((Rep v -> a) -> b)) -> a `e` b
liftE = inE . inV1 . flip


-- Elimination

appE :: EnvPassing v e => a `e` b -> (Rep v -> ((Rep v -> a) -> b))
appE = flip . exE1

appE2 :: EnvPassing v e => a `e` (b `e` c) -> (Rep v -> ((Rep v -> a) -> (Rep v -> b) -> c))
appE2 f s = (`appE` s) . appE f s


(↑) :: EnvPassing v e => a `e` b -> (v a -> v b)
(↑) = exE

infixl 7 ↑

(<↑) :: (EnvPassing v e, Conj c) => (a `c` _Γ) `e` _Δ -> a -> _Γ `e` _Δ
e <↑ a = inE (exE e . fmap (inlr a))

infixl 7 <↑


-- Currying

curryE :: EnvPassing v e => (a, b) `e` d -> a `e` (b `e` d)
curryE c = inE (fmap ((`lmap` c) . (,)))

uncurryE :: EnvPassing v e => a `e` (b `e` c) -> (a, b) `e` c
uncurryE c = inE1 (\ v -> ($ (fst . v, snd . v)) . uncurry . appE2 c)


-- Category

idE :: EnvPassing v e => e a a
idE = inE id

composeE :: EnvPassing v e => e b d -> e a b -> e a d
composeE f g = inE (exE f . exE g)


-- Functor

fmapE :: EnvPassing v e => (b -> b') -> (e a b -> e a b')
fmapE = rmapE


-- Distributive

distributeE :: (EnvPassing v e, Functor f) => f (a `e` b) -> a `e` f b
distributeE r = inE1 (\ a s -> (\ e -> exE1 e a s) <$> r)

collectE :: (EnvPassing v e, Functor f) => (c -> a `e` b) -> f c -> a `e` f b
collectE f r = inE1 (\ a s -> (\ c -> exE1 (f c) a s) <$> r)


-- Representable

tabulateE :: EnvPassing v e => (Store (Rep v) b -> a) -> b `e` a
tabulateE f = inE1 (fmap f . store)

indexE :: EnvPassing v e => b `e` a -> (Store (Rep v) b -> a)
indexE e = uncurry (exE1 e) . runStore


-- Applicative

pureE :: EnvPassing v e => b -> e a b
pureE = inE1 . const . const

apE :: EnvPassing v e => e a (b -> b') -> (e a b -> e a b')
apE f a = inE1 (\ k -> exE1 f k <*> exE1 a k)

liftA2E :: EnvPassing v e => (x -> y -> z) -> e a x -> e a y -> e a z
liftA2E f a b = inE1 (\ k -> f <$> exE1 a k <*> exE1 b k)


-- Monad

bindE :: EnvPassing v e => e a b -> (b -> e a b') -> e a b'
bindE m f = inE1 (\ k -> (`exE1` k) =<< f . exE1 m k)


-- Comonad

extractE :: (EnvPassing v e, Monoid (Rep v), Monoid a) => a `e` b -> b
extractE e = appE e mempty mempty

extendE :: EnvPassing v e => (s `e` a -> b) -> (s `e` a -> s `e` b)
extendE f e = inE1 (\ _ _ -> f e)

duplicateE :: EnvPassing v e => a `e` b -> a `e` (a `e` b)
duplicateE e = inE1 (\ _ _ -> e)


-- Profunctor

dimapE :: EnvPassing v e => (a' -> a) -> (b -> b') -> (e a b -> e a' b')
dimapE f g = under _E (dimap (fmap f) (fmap g))

lmapE :: EnvPassing v e => (a' -> a) -> (e a b -> e a' b)
lmapE = (`dimapE` id)

rmapE :: EnvPassing v e => (b -> b') -> (e a b -> e a b')
rmapE = (id `dimapE`)


-- Cochoice

unleftE  :: EnvPassing v e => Either a d `e` Either b d -> a `e` b
unleftE  e = inE1 (flip go . (Left .))
  where go s = (id <--> go s . pure . Right) . appE e s

unrightE :: EnvPassing v e => Either d a `e` Either d b -> a `e` b
unrightE e = inE1 (flip go . (Right .))
  where go s = (go s . pure . Left <--> id) . appE e s


-- Costrong

unfirstE  :: EnvPassing v e => (a, d) `e` (b, d) -> a `e` b
unfirstE  e = inE1 (\ a s -> let (b, d) = appE e s ((,d) . a) in b)

unsecondE :: EnvPassing v e => (d, a) `e` (d, b) -> a `e` b
unsecondE e = inE1 (\ a s -> let (d, b) = appE e s ((d,) . a) in b)


-- Cosieve

cosieveE :: EnvPassing v e => a `e` b -> (Store (Rep v) a -> b)
cosieveE = indexE


-- Corepresentable

cotabulateE :: EnvPassing v e => (Store (Rep v) a -> b) -> a `e` b
cotabulateE = tabulateE


-- Concrete

newtype E v a b = E { runE :: v a -> v b }

instance Representable v => EnvPassing v (E v) where
  inE = E
  exE = runE

instance Representable v => Functor (E v a) where
  fmap = fmapE

instance Representable v => Distributive (E v a) where
  distribute = distributeE
  collect = collectE

instance Representable v => Representable (E v b) where
  type Rep (E v b) = Store (Rep v) b
  tabulate = tabulateE
  index = indexE

instance Representable v => Applicative (E v a) where
  pure = pureE
  (<*>) = apE
  liftA2 = liftA2E

instance Representable v => Monad (E v a) where
  (>>=) = bindE

instance (Representable v, Monoid (Rep v), Monoid a) => Comonad (E v a) where
  extract = extractE
  extend = extendE
  duplicate = duplicateE

instance Representable v => Cat.Category (E v) where
  id = idE
  (.) = composeE

instance Representable v => Profunctor (E v) where
  dimap = dimapE
  lmap = lmapE
  rmap = rmapE

instance Representable v => Cochoice (E v) where
  unleft = unleftE
  unright = unrightE

instance Representable v => Costrong (E v) where
  unfirst  = unfirstE
  unsecond = unsecondE

instance (Representable v, s ~ Rep v) => Cosieve (E v) (Store s) where
  cosieve = cosieveE

instance Representable v => Pro.Corepresentable (E v) where
  type Corep (E v) = Store (Rep v)

  cotabulate = cotabulateE
