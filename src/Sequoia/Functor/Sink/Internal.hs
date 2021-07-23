module Sequoia.Functor.Sink.Internal
( Snk(..)
) where

import Data.Functor.Contravariant
import Sequoia.Functor.Applicative

newtype Snk e r a = Snk { runSnkFn :: (e -> a) -> (e -> r) }

instance Contravariant (Snk e r) where
  contramap f = Snk . (. fmap f) . runSnkFn

instance Contrapply (Snk e r) where
  contraliftA2 f a b = Snk (\ v -> either (runSnkFn a . pure) (runSnkFn b . pure) . f . v <*> id)
