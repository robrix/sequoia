{-# LANGUAGE TypeFamilies #-}
module Sequoia.Signal
( -- * Signals
  Sol(..)
, Src(..)
, Snk(..)
, Sig(..)
, solSrc
, solSnk
, srcSig
, snkSig
, solSig
, dnKm
  -- Self-adjunction
, self
, Self(..)
  -- Maps
, mapKSol
, mapKSrc
, mapKSnk
, mapKSig
) where

import Control.Category ((<<<))
import Data.Distributive
import Data.Functor.Contravariant.Adjunction hiding (adjuncted)
import Sequoia.Bijection
import Sequoia.Calculus.Context
import Sequoia.Continuation

-- Signals

newtype Sol k     = Sol { runSol :: k Δ -> k Γ }


newtype Src k   b = Src { runSrc :: k **b }

instance Contravariant k => Functor (Src k) where
  fmap f = Src . contramap (contramap f) . runSrc

instance Representable k => Applicative (Src k) where
  pure a = Src (inK (`exK` a))
  Src f <*> Src a = Src (inK (\ b -> exK f (inK (exK a . inK . (exK b .)))))

instance Representable k => Monad (Src k) where
  Src m >>= f = Src (m •<< inK . \ k -> (`exK` k) . runSrc . f)


newtype Snk k a   = Snk { runSnk :: a -> k **Δ }


newtype Sig k a b = Sig { runSig :: k b -> k a }


solSrc
  :: Adjunction k k
  =>      Sol k
           <->
          Src k |- Δ
solSrc = coercedTo Src <<< constant Γ <<< contraadjuncted <<< coercedFrom Sol


solSnk
  :: Adjunction k k
  =>      Sol k
           <->
     Γ -| Snk k
solSnk = coercedTo Snk <<< contraadjuncted <<< coercedFrom Sol


srcSig
  :: Adjunction k k
  =>      Src k |- b
           <->
     Γ -| Sig k |- b
srcSig = coercedTo Sig <<< contraadjuncted <<< inv (constant Γ) <<< coercedFrom Src


snkSig
  :: Adjunction k k
  => a -| Snk k
           <->
     a -| Sig k |- Δ
snkSig = coercedTo Sig <<< contraadjuncted <<< coercedFrom Snk


solSig
  ::      Sol k
           <->
     Γ -| Sig k |- Δ
solSig = coerced


{-
       o
  Sol ---> Src
   │        │
 i │        │ i
   ↓        ↓
  Snk ---> Sig
       o
-}


-- | Witness of the adjunction between the double negation and continuation morphism representations of functions in CPS.
dnKm :: Adjunction j k => (a -> j (k b)) <-> (k b -> k a)
dnKm = leftAdjunct <-> rightAdjunct


-- Self-adjunction

self :: k a <-> Self k a
self = Self <-> getSelf

newtype Self k a = Self { getSelf :: k a }
  deriving (Contravariant, Functor, Representable)

instance Distributive k => Distributive (Self k) where
  distribute = Self . distribute . fmap getSelf

instance Representable k => Adjunction (Self k) (Self k) where
  leftAdjunct  = (-<<)
  rightAdjunct = (-<<)


-- Maps

mapKSol :: (forall x . k x <-> k' x) -> (Sol k -> Sol k')
mapKSol b = Sol . (dimapping b b <~) . runSol

mapKSrc :: Contravariant k => (forall x . k x <-> k' x) -> (Src k b -> Src k' b)
mapKSrc b = Src . mapDN b . runSrc

mapKSnk :: Contravariant k => (forall x . k x <-> k' x) -> (Snk k a -> Snk k' a)
mapKSnk b = Snk . (mapDN b .) . runSnk

mapKSig :: (forall x . k x <-> k' x) -> (Sig k a b -> Sig k' a b)
mapKSig b = Sig . (dimapping b b <~) . runSig
