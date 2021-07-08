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

newtype Sol k     = Sol { runSol :: Sig k Γ Δ }

mapKSol :: (forall x . k x () <-> k' x ()) -> (Sol k -> Sol k')
mapKSol b = Sol . mapKSig b . runSol


newtype Src k   b = Src { runSrc :: Sig k Γ b }
  deriving (Applicative, Functor, Monad)

mapKSrc :: (forall x . k x () <-> k' x ()) -> (Src k b -> Src k' b)
mapKSrc b = Src . mapKSig b . runSrc


newtype Snk k a   = Snk { runSnk :: Sig k a Δ }

mapKSnk :: (forall x . k x () <-> k' x ()) -> (Snk k a -> Snk k' a)
mapKSnk b = Snk . mapKSig b . runSnk


newtype Sig k a b = Sig { runSig :: k b () -> k a () }

instance Cat.Category (Sig k) where
  id = Sig id
  (.) = dimap2 runSig runSig Sig (flip (.))

instance Profunctor k => Profunctor (Sig k) where
  dimap f g = Sig . dimap (lmap g) (lmap f) . runSig

instance Profunctor k => Functor (Sig k a) where
  fmap f = Sig . lmap (lmap f) . runSig

instance Continuation k => Applicative (Sig k a) where
  pure a = Sig (•<< const a)
  Sig f <*> Sig a = Sig (inK1 (\ k a' -> f (inK (\ f -> a (inK (k . f)) • a')) • a'))

instance Continuation k => Monad (Sig k a) where
  Sig m >>= f = Sig (inK1 (\ k a -> m (inK ((• a) . (`runSig` inK k) . f)) • a))

mapKSig :: (forall x . k x () <-> k' x ()) -> (Sig k a b -> Sig k' a b)
mapKSig b = Sig . (~> dimapping b b) . runSig


-- Conversions

solSrc
  ::      Sol k
           <->
          Src k |- Δ
solSrc = coerced


solSnk
  ::      Sol k
           <->
     Γ -| Snk k
solSnk = coerced


srcSig
  ::      Src k |- b
           <->
     Γ -| Sig k |- b
srcSig = coerced

composeSrcSig :: Src k a -> Sig k a b -> Src k b
composeSrcSig src sig = srcSig <~ (sig <<< src ~> srcSig)


snkSig
  :: a -| Snk k
           <->
     a -| Sig k |- Δ
snkSig = coerced

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
