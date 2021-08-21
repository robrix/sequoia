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
, mapSrcFnK
, mapSrcFnC
  -- * Optics
, _SrcExp
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

-- Sources

_Src :: Iso (Src e r b) (Src e' r' b') (b • r -> e |-- r) (b' • r' -> e' |-- r')
_Src = coerced


-- Construction

src :: ((b • r) -> (e |-- r)) -> Src e r b
src = coerce

srcFn :: ((b -> r) -> (e -> r)) -> Src e r b
srcFn = Src

(↑) :: a --|Exp e r|-> b -> e ∘ a -> Src e r|-> b
f ↑ v = src (flip (↓ f) v)

infixl 3 ↑


-- Elimination

runSrc :: Src e r b -> (b • r -> e |-- r)
runSrc = coerce . runSrcFn

elimSrc :: Src e r a -> Snk e r a -> e |-- r
elimSrc sr sn = env (pure . (runSrcFn sr . flip (runSnkFn sn . pure) <*> id))


-- Computation

mapSrcE :: (forall x . e ∘ x -> e' ∘ x) -> (Src e r b -> Src e' r b)
mapSrcE f = over _Src (mapSrcFnC (over _CV f))

mapSrcR :: (forall x . Iso' (x • r) (x • r')) -> (Src e r b -> Src e r' b)
mapSrcR b = over _Src (mapSrcFnC (over _CK (view b)) . mapSrcFnK (review b))

mapSrcFnK :: (forall x . x • r2 -> x • r1) -> (b • r1 -> e |-- r) -> (b • r2 -> e |-- r)
mapSrcFnK = lmap

mapSrcFnC :: (e1 |-- r1 -> e2 |-- r2) -> (b • r -> e1 |-- r1) -> (b • r -> e2 |-- r2)
mapSrcFnC = rmap


-- Optics

_SrcExp :: Iso (Src e r b) (Src e' r' b') (Exp e r e b) (Exp e' r' e' b')
_SrcExp = _Src.from (_Exp.rmapping (constantWith idV (<<∘)))
