{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Functor.V
( V(..)
) where

import Data.Distributive
import Data.Functor.Rep
import Data.Profunctor

newtype V s a = V { runV :: s -> a }
  deriving (Applicative, Choice, Closed, Cochoice, Costrong, Functor, Monad, Monoid, Profunctor, Representable, Semigroup, Strong)

instance Distributive (V s) where
  distribute = distributeRep
  collect = collectRep
