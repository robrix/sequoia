-- | A contravariant functor over a profunctor’s input.
module Sequoia.Functor.In
( In(..)
) where

import Data.Functor.Contravariant
import Data.Profunctor

newtype In p r a = In { runIn :: p a r }

instance Profunctor p => Contravariant (In p r) where
  contramap f = In . lmap f . runIn
