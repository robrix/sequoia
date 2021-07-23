module Sequoia.Functor.Source
( -- * Sources
  _Src
, Src(..)
  -- * Construction
, inSrcFn
, (↑)
  -- * Elimination
, exSrcFn
, elimSrc
  -- * Computation
, mapSrcK
, mapSrcV
  -- * Optics
, _SrcExp
) where

import Data.Coerce
import Data.Profunctor
import Sequoia.Functor.Source.Internal
import Sequoia.Optic.Getter
import Sequoia.Optic.Iso
import Sequoia.Optic.Review
import Sequoia.Optic.Setter
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exponential
import Sequoia.Profunctor.Value

-- Construction

inSrcFn :: ((b -> r) -> (e -> r)) -> Src e r b
inSrcFn = coerce

(↑) :: a --|Exp e r|-> b -> e ∘ a -> Src e r|-> b
f ↑ v = Src (exExp f v)

infixl 3 ↑


-- Elimination

exSrcFn :: Src e r b -> ((b -> r) -> (e -> r))
exSrcFn = coerce . runSrc

-- FIXME: this takes a function instead of a Snk to avoid cyclic module imports, would be nicer to have the definitions pulled out somewhere reasonable
elimSrc :: Src e r a -> (e ∘ a -> e ==> r) -> e ==> r
elimSrc sr sn = cont (\ _K -> runSrc sr (_K (sn . pure)))


-- Computation

mapSrcK :: (forall x . x • r <-> x • r') -> (Src e r b -> Src e r' b)
mapSrcK b = over _Src (dimap (review b) (mapCK (view b)))

mapSrcV :: (forall x . e ∘ x -> e' ∘ x) -> (Src e r b -> Src e' r b)
mapSrcV f = over _Src (fmap (mapCV f))


-- Optics

_SrcExp :: Iso (Src e r b) (Src e' r' b') (Exp e r e b) (Exp e' r' e' b')
_SrcExp = _Src.from (_Exp.constantWith (V id) (flip ((.) . (∘<<))))
