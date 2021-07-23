module Sequoia.Functor.Snk.Internal
( Snk(..)
) where

import Data.Functor.Contravariant
import Sequoia.Disjunction
import Sequoia.Functor.Applicative
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Value

newtype Snk e r a = Snk { runSnk :: e ∘ a -> e ==> r }

instance Contravariant (Snk e r) where
  contramap f = Snk . (. fmap f) . runSnk

instance Contrapply (Snk e r) where
  contraliftA2 f a b = Snk (val ((runSnk a . pure <--> runSnk b . pure) . f))
