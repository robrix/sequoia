{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.EPS
( -- * EPS
  EPFn
, EnvPassing(..)
, _E
, inE1
, exE1
  -- ** Construction
, eps
, liftE
  -- ** Elimination
, appE
  -- ** Category
, idE
, composeE
  -- ** Functor
, fmapE
  -- ** Applicative
, pureE
, apE
, liftA2E
  -- ** Monad
, bindE
  -- ** Profunctor
, dimapE
, lmapE
, rmapE
  -- ** Cosieve
, cosieveE
  -- ** Corepresentable
, cotabulateE
  -- * Concrete
, E(..)
) where

import           Control.Applicative (liftA2)
import qualified Control.Category as Cat
import           Data.Profunctor
import           Sequoia.Bijection
import           Sequoia.Value

-- EPS

type EPFn v a b = v a -> v b

class (Cat.Category e, Value v, Profunctor e) => EnvPassing v e | e -> v where
  inE :: EPFn v a b -> a `e` b
  exE :: a `e` b    -> EPFn v a b


_E :: (EnvPassing v e, EnvPassing v' e') => Optic Iso (e a b) (e' a' b') (EPFn v a b) (EPFn v' a' b')
_E = exE <-> inE


inE1 :: EnvPassing v e => (VFn v a -> VFn v b) -> a `e` b
inE1 = inE . inV1

exE1 :: EnvPassing v e => a `e` b -> (VFn v a -> VFn v b)
exE1 = exV1 . exE


-- Construction

eps :: EnvPassing v e => (a -> b) -> a `e` b
eps = inE1 . (.)

liftE :: EnvPassing v e => (VRep v -> (VRep v -> a) -> b) -> a `e` b
liftE = inE . inV1 . flip


-- Elimination

appE :: EnvPassing v e => a `e` b -> VRep v -> (VRep v -> a) -> b
appE = flip . exE1


-- Category

idE :: EnvPassing v e => e a a
idE = inE id

composeE :: EnvPassing v e => e b d -> e a b -> e a d
composeE f g = inE (exE f . exE g)


-- Functor

fmapE :: EnvPassing v e => (b -> b') -> (e a b -> e a b')
fmapE = rmapE


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


-- Profunctor

dimapE :: EnvPassing v e => (a' -> a) -> (b -> b') -> (e a b -> e a' b')
dimapE f g = under _E (dimap (fmap f) (fmap g))

lmapE :: EnvPassing v e => (a' -> a) -> (e a b -> e a' b)
lmapE = (`dimapE` id)

rmapE :: EnvPassing v e => (b -> b') -> (e a b -> e a b')
rmapE = (id `dimapE`)


-- Cosieve

cosieveE :: EnvPassing v e => a `e` b -> Env v a b
cosieveE = Env . inV . flip . lmap exV . exE1


-- Corepresentable

cotabulateE :: EnvPassing v e => Env v a b -> a `e` b
cotabulateE b = inE1 (\ k s -> appEnv b s (inV k))


-- Concrete

newtype E v a b = E { runE :: v a -> v b }

instance Value v => EnvPassing v (E v) where
  inE = E
  exE = runE

instance Value v => Functor (E v a) where
  fmap = fmapE

instance Value v => Applicative (E v a) where
  pure = pureE
  (<*>) = apE
  liftA2 = liftA2E

instance Value v => Monad (E v a) where
  (>>=) = bindE

instance Value v => Cat.Category (E v) where
  id = idE
  (.) = composeE

instance Value v => Profunctor (E v) where
  dimap = dimapE
  lmap = lmapE
  rmap = rmapE
