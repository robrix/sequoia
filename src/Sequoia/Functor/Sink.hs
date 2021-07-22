module Sequoia.Functor.Sink
( -- * Sinks
  _Snk
, Snk(..)
  -- * Computation
, mapSnkK
, mapSnkV
  -- * Optics
, _SnkExp
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Sequoia.Disjunction
import Sequoia.Functor.Applicative
import Sequoia.Optic.Getter
import Sequoia.Optic.Iso
import Sequoia.Optic.Review
import Sequoia.Optic.Setter
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exponential
import Sequoia.Profunctor.Value

-- Sinks

_Snk :: Iso (Snk e r a) (Snk e' r' a') (e ∘ a -> C e r) (e' ∘ a' -> C e' r')
_Snk = runSnk <-> Snk

newtype Snk e r a = Snk { runSnk :: e ∘ a -> C e r }

instance Contravariant (Snk e r) where
  contramap f = over _Snk (. fmap f)

instance Contrapply (Snk e r) where
  contraliftA2 f a b = Snk (val ((runSnk a . inV0 <--> runSnk b . inV0) . f))


-- Computation

mapSnkK :: (forall x . x • r -> x • r') -> (Snk e r a -> Snk e r' a)
mapSnkK f = over _Snk (fmap (mapCK f))

mapSnkV :: (forall x . e ∘ x <-> e' ∘ x) -> (Snk e r a -> Snk e' r a)
mapSnkV b = over _Snk (dimap (review b) (mapCV (view b)))


-- Optics

_SnkExp :: (Exponential f, Exponential f') => Iso (Snk e r a) (Snk e' r' a') (f e r a r) (f' e' r' a' r')
_SnkExp = _Snk.from (_Exponential.rmapping (constant (K id)))
