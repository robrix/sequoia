{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Context
( C(..)
) where

import Control.Category as Cat
import Data.Distributive
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Traversing

newtype C e r = C { runC :: e -> r }
  deriving (Applicative, Cat.Category, Choice, Closed, Cochoice, Costrong, Functor, Mapping, Monad, Profunctor, Co.Representable, Strong, Traversing)

instance Distributive (C e) where
  distribute = distributeRep
  collect = collectRep
