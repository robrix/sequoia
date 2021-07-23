module Sequoia.Functor.Sink
( -- * Sinks
  _Snk
, Snk(..)
  -- * Construction
, snk
, snkFn
, (↓)
  -- * Elimination
, runSnk
, elimSnk
  -- * Computation
, mapSnkK
, mapSnkV
  -- * Optics
, _SnkExp
) where

import Data.Coerce
import Data.Profunctor
import Sequoia.Functor.Snk.Internal
import Sequoia.Functor.Source.Internal
import Sequoia.Optic.Getter
import Sequoia.Optic.Iso
import Sequoia.Optic.Review
import Sequoia.Optic.Setter
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exponential
import Sequoia.Profunctor.Value

-- Sinks

_Snk :: Iso (Snk e r a) (Snk e' r' a') (e ∘ a -> e ==> r) (e' ∘ a' -> e' ==> r')
_Snk = coerced


-- Construction

snk :: (e ∘ a -> e ==> r) -> Snk e r a
snk = coerce

snkFn :: ((e -> a) -> (e -> r)) -> Snk e r a
snkFn = coerce

(↓) :: b • r -> a --|Exp e r|-> b -> a --|Snk e r
k ↓ f = snk (flip (runExp f) k)

infixl 2 ↓


-- Elimination

runSnk :: Snk e r a -> (e ∘ a -> e ==> r)
runSnk = coerce . runSnk

-- FIXME: this takes a function instead of a Src to avoid cyclic module imports, would be nicer to have the definitions pulled out somewhere reasonable
elimSnk :: Snk e r a -> Src e r a -> e ==> r
elimSnk sn sr = env (res . (runSrcFn sr . flip (runSnkFn sn . pure) <*> id))


-- Computation

mapSnkK :: (forall x . x • r -> x • r') -> (Snk e r a -> Snk e r' a)
mapSnkK f = over _Snk (fmap (mapCK f))

mapSnkV :: (forall x . e ∘ x <-> e' ∘ x) -> (Snk e r a -> Snk e' r a)
mapSnkV b = over _Snk (dimap (review b) (mapCV (view b)))


-- Optics

_SnkExp :: Iso (Snk e r a) (Snk e' r' a') (Exp e r a r) (Exp e' r' a' r')
_SnkExp = _Snk.from (_Exp.rmapping (constantWith (K id) (>>•)))
