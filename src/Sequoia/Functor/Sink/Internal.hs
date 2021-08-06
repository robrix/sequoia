module Sequoia.Functor.Sink.Internal
( Snk(..)
) where

import Data.Functor.Contravariant
import Sequoia.Functor.Applicative
import Sequoia.Profunctor.Coexponential
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

newtype Snk e r a = Snk { runSnkFn :: (e -> a) -> (e -> r) }

instance Contravariant (Snk e r) where
  contramap f = Snk . (. fmap f) . runSnkFn

instance Contrapply (Coexp e r) (Snk e r) where
  coliftC2 f a b = Snk (\ v e -> runSnkFn a (\ e -> f (V v -< K (flip (runSnkFn b) e . const))) e)
