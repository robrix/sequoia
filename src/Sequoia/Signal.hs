{-# LANGUAGE TypeFamilies #-}
module Sequoia.Signal
( -- * Signals
  Sol(..)
, mapKSol
, mapVSol
, Src(..)
, mapKSrc
, mapVSrc
, Snk(..)
, mapKSnk
, mapVSnk
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
import           Sequoia.Continuation as K
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Optic.Getter
import           Sequoia.Optic.Iso
import           Sequoia.Optic.Review
import           Sequoia.Value as V

-- Signals

(•∘) :: K r a -> V e a -> Sol e r
k •∘ a = Sol (\ e -> k • e ∘ a)

infix 7 •∘

withEnv :: (e -> Sol e r) -> Sol e r
withEnv f = Sol (runSol =<< f)

liftSolWithK :: ((Sol e r -> r) -> Sol e r) -> Sol e r
liftSolWithK f = withEnv (f . flip runSol)


newtype Sol e r     = Sol { runSol :: e -> r }

mapKSol :: (forall x . K r x -> K r' x) -> (Sol e r -> Sol e r')
mapKSol f (Sol r) = Sol (under _K f r)

mapVSol :: (forall x . V e x -> V e' x) -> (Sol e r -> Sol e' r)
mapVSol f (Sol r) = Sol (under _V f r)


newtype Src e r   b = Src { runSrc :: K r b -> Sol e r }

instance Functor (Src e r) where
  fmap f (Src r) = Src (lmap (contramap f) r)

mapKSrc :: (forall x . K r x <-> K r' x) -> (Src e r b -> Src e r' b)
mapKSrc b = Src . dimap (b <~) (mapKSol (~> b)) . runSrc

mapVSrc :: (forall x . V e x -> V e' x) -> (Src e r b -> Src e' r b)
mapVSrc f = Src . rmap (mapVSol f) . runSrc


newtype Snk e r a   = Snk { runSnk :: V e a -> Sol e r }

instance Contravariant (Snk e r) where
  contramap f = Snk . lmap (fmap f) . runSnk

mapKSnk :: (forall x . K r x -> K r' x) -> (Snk e r a -> Snk e r' a)
mapKSnk f = Snk . fmap (mapKSol f) . runSnk

mapVSnk :: (forall x . V e x <-> V e' x) -> (Snk e r a -> Snk e' r a)
mapVSnk b = Snk . dimap (b <~) (mapVSol (~> b)) . runSnk


newtype Sig e r a b = Sig { runSig :: V e a -> K r b -> Sol e r }

instance Cat.Category (Sig e r) where
  id = Sig (flip (•∘))
  Sig f . Sig g = Sig (\ a c -> liftSolWithK (\ go -> g a (inK (go . (`f` c) . inV0))))

instance Profunctor (Sig e r) where
  dimap f g = Sig . dimap (fmap f) (lmap (contramap g)) . runSig

instance Functor (Sig e r a) where
  fmap = rmap

instance Applicative (Sig e r a) where
  pure a = Sig (const (•∘ inV0 a))
  (<*>) = ap

instance Monad (Sig e r a) where
  Sig m >>= f = Sig (\ a b -> liftSolWithK (\ go -> m a (inK (\ a' -> go (runSig (f a') a b)))))

mapKSig :: (forall x . K r x <-> K r' x) -> (Sig e r a b -> Sig e r' a b)
mapKSig b = Sig . fmap (dimap (b <~) (mapKSol (~> b))) . runSig

mapVSig :: (forall x . V e x <-> V e' x) -> (Sig e r a b -> Sig e' r a b)
mapVSig b = Sig . dimap (b <~) (rmap (mapVSol (~> b))) . runSig


-- Conversions

solSrc
  ::      Sol e r
            <->
          Src e r |- r
solSrc = Src . const <-> ($ idK) . runSrc


solSnk
  ::      Sol e r
            <->
     e -| Snk e r
solSnk = Snk . const <-> ($ idV) . runSnk


srcSig
  ::      Src e r |- b
            <->
     e -| Sig e r |- b
srcSig = Sig . const . runSrc <-> Src . ($ idV) . runSig

composeSrcSig :: Src e r a -> Sig e r a b -> Src e r b
composeSrcSig src sig = srcSig <~ (sig <<< src ~> srcSig)


snkSig
  :: a -| Snk e r
            <->
     a -| Sig e r |- r
snkSig = Sig . fmap const . runSnk <-> Snk . fmap ($ idK) . runSig

composeSigSnk :: Sig e r a b -> Snk e r b -> Snk e r a
composeSigSnk sig snk = snkSig <~ (snk ~> snkSig <<< sig)


solSig
  ::      Sol e r
            <->
     e -| Sig e r |- r
solSig = Sig . const . const <-> ($ idK) . ($ idV) . runSig


composeSrcSnk :: Src e r a -> Snk e r a -> Sol e r
composeSrcSnk src snk = solSig <~ (snk ~> snkSig <<< src ~> srcSig)


{-
       o
  Sol ---> Src
   │        │
 i │        │ i
   ↓        ↓
  Snk ---> Sig
       o
-}
