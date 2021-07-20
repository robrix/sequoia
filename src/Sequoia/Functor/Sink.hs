module Sequoia.Functor.Sink
( -- * Sinks
  Snk(..)
) where

import Data.Functor.Contravariant
import Sequoia.Functor.V
import Sequoia.Profunctor.Context

-- Sinks

newtype Snk e r a = Snk { runSnk :: V e a -> C e r }

instance Contravariant (Snk e r) where
  contramap f = Snk . (. fmap f) . runSnk
