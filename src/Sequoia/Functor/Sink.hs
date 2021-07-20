module Sequoia.Functor.Sink
( -- * Sinks
  Snk(..)
) where

import Sequoia.Functor.V
import Sequoia.Profunctor.Context

-- Sinks

newtype Snk e r a = Snk { runSnk :: V e a -> C e r }
