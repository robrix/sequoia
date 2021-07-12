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
) where

import           Control.Category ((<<<))
import qualified Control.Category as Cat
import           Data.Profunctor
import           Sequoia.Bijection
import           Sequoia.Calculus.Context
import           Sequoia.Continuation

-- Signals

newtype Sol k v     = Sol { runSol :: Sig k v Γ Δ }

mapKSol :: (forall x . k x <-> k' x) -> (Sol k v -> Sol k' v)
mapKSol b = Sol . mapKSig b . runSol


newtype Src k v   b = Src { runSrc :: Sig k v Γ b }
  deriving (Applicative, Functor, Monad)

mapKSrc :: (forall x . k x <-> k' x) -> (Src k v b -> Src k' v b)
mapKSrc b = Src . mapKSig b . runSrc


newtype Snk k v a   = Snk { runSnk :: Sig k v a Δ }

mapKSnk :: (forall x . k x <-> k' x) -> (Snk k v a -> Snk k' v a)
mapKSnk b = Snk . mapKSig b . runSnk


newtype Sig k v a b = Sig { runSig :: k b -> k a }

instance Cat.Category (Sig k v) where
  id = Sig id
  (.) = dimap2 runSig runSig Sig (flip (.))

instance Contravariant k => Profunctor (Sig k v) where
  dimap f g = Sig . dimap (contramap g) (contramap f) . runSig

instance Contravariant k => Functor (Sig k v a) where
  fmap f = Sig . lmap (contramap f) . runSig

instance Continuation k => Applicative (Sig k v a) where
  pure a = Sig (•<< const a)
  Sig f <*> Sig a = Sig (inK1 (\ k a' -> f (inK (\ f -> a (inK (k . f)) • a')) • a'))

instance Continuation k => Monad (Sig k v a) where
  Sig m >>= f = Sig (inK1 (\ k a -> m (inK ((• a) . (`runSig` inK k) . f)) • a))

mapKSig :: (forall x . k x <-> k' x) -> (Sig k v a b -> Sig k' v a b)
mapKSig b = Sig . (~> dimapping b b) . runSig


-- Conversions

solSrc
  ::      Sol k v
            <->
          Src k v |- Δ
solSrc = coerced


solSnk
  ::      Sol k v
            <->
     Γ -| Snk k v
solSnk = coerced


srcSig
  ::      Src k v |- b
            <->
     Γ -| Sig k v |- b
srcSig = coerced

composeSrcSig :: Src k v a -> Sig k v a b -> Src k v b
composeSrcSig src sig = srcSig <~ (sig <<< src ~> srcSig)


snkSig
  :: a -| Snk k v
            <->
     a -| Sig k v |- Δ
snkSig = coerced

composeSigSnk :: Sig k v a b -> Snk k v b -> Snk k v a
composeSigSnk sig snk = snkSig <~ (snk ~> snkSig <<< sig)


solSig
  ::      Sol k v
            <->
     Γ -| Sig k v |- Δ
solSig = coerced


composeSrcSnk :: Src k v a -> Snk k v a -> Sol k v
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
