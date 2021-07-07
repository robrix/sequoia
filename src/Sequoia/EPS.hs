{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.EPS
( -- * EPS
  EPFn
, EnvPassing(..)
) where

import qualified Control.Category as Cat
import           Data.Profunctor
import           Sequoia.Value

-- EPS

type EPFn v a b = v a -> v b

class (Cat.Category e, Value v, Profunctor e) => EnvPassing v e | e -> v where
  inE :: EPFn v a b -> a `e` b
  exE :: a `e` b    -> EPFn v a b
