{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.EPS
( -- * EPS
  EPFn
, EnvPassing(..)
, _E
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
