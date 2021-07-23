module Sequoia.Functor.Source
( -- * Sources
  _Src
, Src(..)
  -- * Construction
, src
, srcFn
, (↑)
  -- * Elimination
, runSrc
, elimSrc
  -- * Computation
, mapSrcK
, mapSrcV
  -- * Optics
, _SrcExp
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

-- Sources

_Src :: Iso (Src e r b) (Src e' r' b') (b • r -> e ==> r) (b' • r' -> e' ==> r')
_Src = coerced


-- Construction

src :: ((b • r) -> (e ==> r)) -> Src e r b
src = coerce

srcFn :: ((b -> r) -> (e -> r)) -> Src e r b
srcFn = Src

(↑) :: a --|Exp e r|-> b -> e ∘ a -> Src e r|-> b
f ↑ v = Src (exExpFn f (v ∘))

infixl 3 ↑


-- Elimination

runSrc :: Src e r b -> ((b • r) -> (e ==> r))
runSrc = coerce . runSrcFn

-- FIXME: this takes a function instead of a Snk to avoid cyclic module imports, would be nicer to have the definitions pulled out somewhere reasonable
elimSrc :: Src e r a -> Snk e r a -> e ==> r
elimSrc sr sn = env (res . (runSrcFn sr . flip (runSnkFn sn . pure) <*> id))


-- Computation

mapSrcK :: (forall x . x • r <-> x • r') -> (Src e r b -> Src e r' b)
mapSrcK b = over _Src (dimap (review b) (mapCK (view b)))

mapSrcV :: (forall x . e ∘ x -> e' ∘ x) -> (Src e r b -> Src e' r b)
mapSrcV f = over _Src (fmap (mapCV f))


-- Optics

_SrcExp :: Iso (Src e r b) (Src e' r' b') (Exp e r e b) (Exp e' r' e' b')
_SrcExp = _Src.from (_Exp.constantWith (V id) (flip ((.) . (∘<<))))
