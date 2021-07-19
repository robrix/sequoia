module Sequoia.Optic.Lens
( -- * Lenses
  Lens
, Lens'
, lens
, _fst
, _snd
) where

import Data.Profunctor
import Sequoia.Bijection

-- Lenses

type Lens s t a b = forall p . Strong p => Optic p s t a b

type Lens' s a = Lens s s a a

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens prj inj = dimap (\ s -> (prj s, s)) (\ (b, s) -> inj s b) . first'


_fst :: Lens (a, b) (a', b) a a'
_fst = lens fst (\ ~(_, b) a' -> (a', b))

_snd :: Lens (a, b) (a, b') b b'
_snd = lens snd (\ ~(a, _) b' -> (a, b'))
