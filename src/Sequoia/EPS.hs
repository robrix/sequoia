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
) where

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
