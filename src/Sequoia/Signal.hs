{-# LANGUAGE TypeFamilies #-}
module Sequoia.Signal
( -- * Signals
  _Sig
, Sig(..)
, mapKSig
, mapVSig
  -- * Conversions
, solSrc
, solSnk
, srcSig
, composeSrcSig
, snkSig
, composeSigSnk
, solSig
, composeSrcSnk
) where

import           Control.Category ((<<<))
import qualified Control.Category as Cat
import           Control.Monad (ap)
import           Data.Profunctor
import           Sequoia.Calculus.Context
import           Sequoia.Functor.Sink
import           Sequoia.Functor.Source
import           Sequoia.Optic.Getter
import           Sequoia.Optic.Iso
import           Sequoia.Optic.Review
import           Sequoia.Profunctor.Context
import           Sequoia.Profunctor.Continuation as K
import           Sequoia.Profunctor.Value as V

-- Signals

_Sig :: Iso (Sig e r a b) (Sig e' r' a' b') (e ∘ a -> b • r -> e ==> r) (e' ∘ a' -> b' • r' -> e' ==> r')
_Sig = coerced

newtype Sig e r a b = Sig { runSig :: e ∘ a -> b • r -> e ==> r }

instance Cat.Category (Sig e r) where
  id = Sig (flip (•∘))
  Sig f . Sig g = Sig (\ a c -> liftRes (\ go -> g a (K (go . (`f` c) . pure))))

instance Profunctor (Sig e r) where
  dimap f g = Sig . dimap (fmap f) (lmap (lmap g)) . runSig

instance Functor (Sig e r a) where
  fmap = rmap

instance Applicative (Sig e r a) where
  pure = Sig . const . flip (••)
  (<*>) = ap

instance Monad (Sig e r a) where
  Sig m >>= f = Sig (\ a b -> liftRes (\ go -> m a (K (\ a' -> go (runSig (f a') a b)))))

mapKSig :: (forall x . x • r <-> x • r') -> (Sig e r a b -> Sig e r' a b)
mapKSig b = Sig . fmap (dimap (review b) (mapCK (view b))) . runSig

mapVSig :: (forall x . e ∘ x <-> e' ∘ x) -> (Sig e r a b -> Sig e' r a b)
mapVSig b = Sig . dimap (review b) (rmap (mapCV (view b))) . runSig


-- Conversions

solSrc
  ::      e ==> r
            <->
          Src e r |- r
solSrc = src . const <-> ($ K id) . runSrc


solSnk
  ::      e ==> r
            <->
     e -| Snk e r
solSnk = Snk . const <-> ($ V id) . runSnk


srcSig
  ::      Src e r |- b
            <->
     e -| Sig e r |- b
srcSig = _Src.from (_Sig.constantWith (V id) (flip ((.) . (∘<<))))

composeSrcSig :: Src e r a -> Sig e r a b -> Src e r b
composeSrcSig src sig = review srcSig (sig <<< view srcSig src)


snkSig
  :: a -| Snk e r
            <->
     a -| Sig e r |- r
snkSig = _Snk.from (_Sig.rmapping (constantWith (K id) (>>•)))

composeSigSnk :: Sig e r a b -> Snk e r b -> Snk e r a
composeSigSnk sig snk = review snkSig (view snkSig snk <<< sig)


solSig
  ::      e ==> r
            <->
     e -| Sig e r |- r
solSig = Sig . const . const <-> ($ K id) . ($ V id) . runSig


composeSrcSnk :: Src e r a -> Snk e r a -> e ==> r
composeSrcSnk src snk = review solSig (snk^.snkSig <<< view srcSig src)


{-
       o
   C  ---> Src
   │        │
 i │        │ i
   ↓        ↓
  Snk ---> Sig
       o
-}
