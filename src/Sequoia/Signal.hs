{-# LANGUAGE TypeFamilies #-}
module Sequoia.Signal
( -- * Signals
  C(..)
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
import           Sequoia.Functor.Continuation as K
import           Sequoia.Functor.Sink
import           Sequoia.Functor.Source
import           Sequoia.Optic.Getter
import           Sequoia.Optic.Iso
import           Sequoia.Optic.Review
import           Sequoia.Profunctor.Context
import           Sequoia.Profunctor.Value as V

-- Signals

newtype Sig e r a b = Sig { runSig :: V e a -> K r b -> C e r }

instance Cat.Category (Sig e r) where
  id = Sig (flip (•∘))
  Sig f . Sig g = Sig (\ a c -> liftRes (\ go -> g a (K (go . (`f` c) . inV0))))

instance Profunctor (Sig e r) where
  dimap f g = Sig . dimap (fmap f) (lmap (contramap g)) . runSig

instance Functor (Sig e r a) where
  fmap = rmap

instance Applicative (Sig e r a) where
  pure a = Sig (const (•∘ inV0 a))
  (<*>) = ap

instance Monad (Sig e r a) where
  Sig m >>= f = Sig (\ a b -> liftRes (\ go -> m a (K (\ a' -> go (runSig (f a') a b)))))

mapKSig :: (forall x . K r x <-> K r' x) -> (Sig e r a b -> Sig e r' a b)
mapKSig b = Sig . fmap (dimap (review b) (mapCK (view b))) . runSig

mapVSig :: (forall x . V e x <-> V e' x) -> (Sig e r a b -> Sig e' r a b)
mapVSig b = Sig . dimap (review b) (rmap (mapCV (view b))) . runSig


-- Conversions

solSrc
  ::       C e r
            <->
          Src e r |- r
solSrc = Src . const <-> ($ idK) . runSrc


solSnk
  ::       C e r
            <->
     e -| Snk e r
solSnk = Snk . const <-> ($ idV) . runSnk


srcSig
  ::      Src e r |- b
            <->
     e -| Sig e r |- b
srcSig = Sig . const . runSrc <-> Src . ($ idV) . runSig

composeSrcSig :: Src e r a -> Sig e r a b -> Src e r b
composeSrcSig src sig = review srcSig (sig <<< view srcSig src)


snkSig
  :: a -| Snk e r
            <->
     a -| Sig e r |- r
snkSig = Sig . fmap const . runSnk <-> Snk . fmap ($ idK) . runSig

composeSigSnk :: Sig e r a b -> Snk e r b -> Snk e r a
composeSigSnk sig snk = review snkSig (view snkSig snk <<< sig)


solSig
  ::       C e r
            <->
     e -| Sig e r |- r
solSig = Sig . const . const <-> ($ idK) . ($ idV) . runSig


composeSrcSnk :: Src e r a -> Snk e r a -> C e r
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
