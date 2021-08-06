module Sequoia.Functor.Sink.Internal
( Snk(..)
) where

import Data.Functor.Contravariant
import Sequoia.Functor.Applicative
import Sequoia.Profunctor.Exp

newtype Snk e r a = Snk { runSnkFn :: (e -> a) -> (e -> r) }

instance Contravariant (Snk e r) where
  contramap f = Snk . (. fmap f) . runSnkFn

instance Contrapply (Coexp r) (Snk e r) where
  coliftC2 f a b = Snk (\ v e -> runSnkFn a (\ e -> f (flip (runSnkFn b) e . const :>- v e)) e)
