module Sequoia.Functor.Source
( -- * Sources
  _Src
, Src(..)
  -- * Construction
, inSrcFn
, (↑)
  -- * Elimination
, exSrcFn
  -- * Computation
, mapSrcK
, mapSrcV
  -- * Optics
, _SrcExp
) where

import Data.Coerce
import Data.Profunctor
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

newtype Src e r b = Src { runSrc :: b • r -> e ==> r }

instance Functor (Src e r) where
  fmap f = over _Src (. lmap f)

instance Applicative (Src e r) where
  pure = Src . fmap res . flip (•)
  Src f <*> Src a = Src (\ k -> cont (\ _K -> f (_K (\ f -> a (K ((k •) . f))))))

instance Monad (Src e r) where
  Src m >>= f = Src (\ k -> cont (\ _K -> m (_K ((`runSrc` k) . f))))

instance Env e (Src e r b) where
  env f = Src (\ k -> env ((`runSrc` k) . f))

instance Res r (Src e r b) where
  res = Src . const . res
  liftRes f = Src (\ k -> liftRes (\ run -> runSrc (f (run . (`runSrc` k))) k))


-- Construction

inSrcFn :: ((b -> r) -> (e -> r)) -> Src e r b
inSrcFn = coerce

(↑) :: a --|Exp e r|-> b -> e ∘ a -> Src e r|-> b
f ↑ v = Src (exExp f v)


-- Elimination

exSrcFn :: Src e r b -> ((b -> r) -> (e -> r))
exSrcFn = coerce . runSrc


-- Computation

mapSrcK :: (forall x . x • r <-> x • r') -> (Src e r b -> Src e r' b)
mapSrcK b = over _Src (dimap (review b) (mapCK (view b)))

mapSrcV :: (forall x . e ∘ x -> e' ∘ x) -> (Src e r b -> Src e' r b)
mapSrcV f = over _Src (fmap (mapCV f))


-- Optics

_SrcExp :: Iso (Src e r b) (Src e' r' b') (Exp e r e b) (Exp e' r' e' b')
_SrcExp = _Src.from (_Exp.constant (V id))
