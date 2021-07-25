module Sequoia.Functor.Source
( -- * Sources
  _Src
, Src(..)
  -- * Construction
, src
, srcFn
, (Sequoia.Functor.Source.↑)
  -- * Elimination
, runSrc
, elimSrc
  -- * Computation
, mapSrcE
, mapSrcR
  -- * Optics
, _SrcExp
) where

import Data.Coerce
import Data.Profunctor
import Sequoia.Functor.Sink.Internal
import Sequoia.Functor.Source.Internal
import Sequoia.Optic.Getter
import Sequoia.Optic.Iso
import Sequoia.Optic.Review
import Sequoia.Optic.Setter
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exponential as Exp
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
f ↑ v = src (flip (↓ f) v)

infixl 3 ↑


-- Elimination

runSrc :: Src e r b -> (b • r -> e ==> r)
runSrc = coerce . runSrcFn

-- FIXME: this takes a function instead of a Snk to avoid cyclic module imports, would be nicer to have the definitions pulled out somewhere reasonable
elimSrc :: Src e r a -> Snk e r a -> e ==> r
elimSrc sr sn = env (pure . (runSrcFn sr . flip (runSnkFn sn . pure) <*> id))


-- Computation

mapSrcE :: (forall x . e ∘ x -> e' ∘ x) -> (Src e r b -> Src e' r b)
mapSrcE f = over _Src (fmap (over _CV f))

mapSrcR :: (forall x . x • r <-> x • r') -> (Src e r b -> Src e r' b)
mapSrcR b = over _Src (dimap (review b) (over _CK (view b)))


-- Optics

_SrcExp :: Iso (Src e r b) (Src e' r' b') (Exp e r e b) (Exp e' r' e' b')
_SrcExp = _Src.from (_Exp.rmapping (constantWith idV (<<∘)))
