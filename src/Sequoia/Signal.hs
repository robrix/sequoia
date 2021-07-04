{-# LANGUAGE TypeFamilies #-}
module Sequoia.Signal
( -- * Signals
  Sol(..)
, mapKSol
, Src(..)
, mapKSrc
, Snk(..)
, mapKSnk
, Sig(..)
, mapKSig
  -- * Conversions
, solSrc
, solSnk
, srcSig
, composeSrcSig
, snkSig
, composeSigSnk
, solSig
, composeSrcSnk
  -- Self-adjunction
, self
, Self(..)
) where

import           Control.Category ((<<<))
import qualified Control.Category as Cat
import           Data.Distributive
import           Data.Functor.Contravariant.Adjunction hiding (adjuncted)
import           Data.Profunctor
import           Sequoia.Bijection
import           Sequoia.Calculus.Context
import           Sequoia.Continuation

-- Signals

newtype Sol k     = Sol { runSol :: k Δ -> k Γ }

mapKSol :: (forall x . k x <-> k' x) -> (Sol k -> Sol k')
mapKSol b = Sol . (~> dimapping b b) . runSol


newtype Src k   b = Src { runSrc :: k b -> k Γ }

instance Contravariant k => Functor (Src k) where
  fmap f = Src . lmap (contramap f) . runSrc

instance Representable k => Applicative (Src k) where
  pure a = Src (•<< const a)
  Src f <*> Src a = Src (inK1 (\ k a' -> exK (f (inK (\ f -> exK (a (inK (k . f))) a'))) a'))

instance Representable k => Monad (Src k) where
  Src m >>= f = Src (inK1 (\ k a -> exK (m (inK ((`exK` a) . (`runSrc` inK k) . f))) a))

mapKSrc :: (forall x . k x <-> k' x) -> (Src k b -> Src k' b)
mapKSrc b = Src . (~> dimapping b b) . runSrc


newtype Snk k a   = Snk { runSnk :: k Δ -> k a }

mapKSnk :: (forall x . k x <-> k' x) -> (Snk k a -> Snk k' a)
mapKSnk b = Snk . (~> dimapping b b) . runSnk


newtype Sig k a b = Sig { runSig :: k b -> k a }

instance Cat.Category (Sig k) where
  id = Sig id
  (.) = dimap2 runSig runSig Sig (flip (.))

instance Contravariant k => Functor (Sig k a) where
  fmap f = Sig . lmap (contramap f) . runSig

mapKSig :: (forall x . k x <-> k' x) -> (Sig k a b -> Sig k' a b)
mapKSig b = Sig . (~> dimapping b b) . runSig


-- Conversions

solSrc
  ::      Sol k
           <->
          Src k |- Δ
solSrc = coercedTo Src <<< coercedFrom Sol


solSnk
  ::      Sol k
           <->
     Γ -| Snk k
solSnk = coercedTo Snk <<< coercedFrom Sol


srcSig
  ::      Src k |- b
           <->
     Γ -| Sig k |- b
srcSig = coercedTo Sig <<< coercedFrom Src

composeSrcSig :: Src k a -> Sig k a b -> Src k b
composeSrcSig src sig = srcSig <~ (sig <<< src ~> srcSig)


snkSig
  :: a -| Snk k
           <->
     a -| Sig k |- Δ
snkSig = coercedTo Sig <<< coercedFrom Snk

composeSigSnk :: Sig k a b -> Snk k b -> Snk k a
composeSigSnk sig snk = snkSig <~ (snk ~> snkSig <<< sig)


solSig
  ::      Sol k
           <->
     Γ -| Sig k |- Δ
solSig = coerced


composeSrcSnk :: Src k a -> Snk k a -> Sol k
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
