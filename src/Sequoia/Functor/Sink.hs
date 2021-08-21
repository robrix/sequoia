module Sequoia.Functor.Sink
( -- * Sinks
  _Snk
, Snk(..)
  -- * Construction
, snk
, snkFn
, (Sequoia.Functor.Sink.↓)
  -- * Elimination
, runSnk
, elimSnk
  -- * Computation
, mapSnkE
, mapSnkR
, mapSnkFnV
, mapSnkFnC
  -- * Optics
, _SnkExp
) where

import Data.Coerce
import Data.Profunctor
import Fresnel.Getter
import Fresnel.Iso
import Fresnel.Review
import Fresnel.Setter
import Sequoia.Functor.Sink.Internal
import Sequoia.Functor.Source.Internal
import Sequoia.Profunctor.Command
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exponential as Exp
import Sequoia.Profunctor.Value

-- Sinks

_Snk :: Iso (Snk e r a) (Snk e' r' a') (e ∘ a -> e |-- r) (e' ∘ a' -> e' |-- r')
_Snk = coerced


-- Construction

snk :: (e ∘ a -> e |-- r) -> Snk e r a
snk = coerce

snkFn :: ((e -> a) -> (e -> r)) -> Snk e r a
snkFn = coerce

(↓) :: b • r -> a --|Exp e r|-> b -> a --|Snk e r
k ↓ f = snk (k Exp.↓ f)

infixl 2 ↓


-- Elimination

runSnk :: Snk e r a -> (e ∘ a -> e |-- r)
runSnk = coerce . runSnk

elimSnk :: Snk e r a -> Src e r a -> e |-- r
elimSnk sn sr = env (pure . (runSrcFn sr . flip (runSnkFn sn . pure) <*> id))


-- Computation

mapSnkE :: (forall x . Iso' (e ∘ x) (e' ∘ x)) -> (Snk e r a -> Snk e' r a)
mapSnkE b = over _Snk (mapSnkFnC (over _CV (view b)) . mapSnkFnV (review b))

mapSnkR :: (forall x . x • r -> x • r') -> (Snk e r a -> Snk e r' a)
mapSnkR f = over _Snk (mapSnkFnC (over _CK f))

mapSnkFnV :: (forall x . e2 ∘ x -> e1 ∘ x) -> (e1 ∘ a -> e |-- r) -> (e2 ∘ a -> e |-- r)
mapSnkFnV = lmap

mapSnkFnC :: (e1 |-- r1 -> e2 |-- r2) -> (e ∘ a -> e1 |-- r1) -> (e ∘ a -> e2 |-- r2)
mapSnkFnC = rmap


-- Optics

_SnkExp :: Iso (Snk e r a) (Snk e' r' a') (Exp e r a r) (Exp e' r' a' r')
_SnkExp = _Snk.from (_Exp.constantWith idK (flip ((.) . (•<<))))
