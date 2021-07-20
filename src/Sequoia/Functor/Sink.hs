module Sequoia.Functor.Sink
( -- * Sinks
  Snk(..)
) where

import Data.Functor.Contravariant
import Sequoia.Disjunction
import Sequoia.Functor.Applicative
import Sequoia.Functor.V
import Sequoia.Profunctor.Context
import Sequoia.Value

-- Sinks

newtype Snk e r a = Snk { runSnk :: V e a -> C e r }

instance Contravariant (Snk e r) where
  contramap f = Snk . (. fmap f) . runSnk

instance Contrapply (Snk e r) where
  contraliftA2 f a b = Snk (val ((runSnk a . inV0 <--> runSnk b . inV0) . f))
