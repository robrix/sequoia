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
import           Sequoia.Bijection
import           Sequoia.Calculus.Context
import           Sequoia.Continuation as K
import           Sequoia.Value as V

-- Signals

(••) :: (K.Representable k, V.Representable v) => k a -> v a -> Sol v k
k •• a = Sol (\ e -> k • e ∘ a)

infix 7 ••

withEnv :: (V.Rep v -> Sol v k) -> Sol v k
withEnv f = Sol (runSol =<< f)

liftSolWithK :: ((Sol v k -> K.Rep k) -> Sol v k) -> Sol v k
liftSolWithK f = withEnv (f . flip runSol)


newtype Sol v k     = Sol { runSol :: V.Rep v -> K.Rep k }

mapKSol :: (K.Representable k, K.Representable k') => (forall x . k x -> k' x) -> (Sol v k -> Sol v k')
mapKSol f (Sol r) = Sol (over _K f r)

mapVSol :: (V.Representable v, V.Representable v') => (forall x . v x -> v' x) -> (Sol v k -> Sol v' k)
mapVSol f (Sol r) = Sol (over _V f r)


newtype Src v k   b = Src { runSrc :: k b -> Sol v k }

instance Contravariant k => Functor (Src v k) where
  fmap f (Src r) = Src (lmap (contramap f) r)

mapKSrc :: (K.Representable k, K.Representable k') => (forall x . k x <-> k' x) -> (Src v k b -> Src v k' b)
mapKSrc b = Src . dimap (b <~) (mapKSol (~> b)) . runSrc

mapVSrc :: (V.Representable v, V.Representable v') => (forall x . v x -> v' x) -> (Src v k b -> Src v' k b)
mapVSrc f = Src . rmap (mapVSol f) . runSrc


newtype Snk v k a   = Snk { runSnk :: v a -> Sol v k }

instance Functor v => Contravariant (Snk v k) where
  contramap f = Snk . lmap (fmap f) . runSnk

mapKSnk :: (K.Representable k, K.Representable k') => (forall x . k x -> k' x) -> (Snk v k a -> Snk v k' a)
mapKSnk f = Snk . fmap (mapKSol f) . runSnk

mapVSnk :: (V.Representable v, V.Representable v') => (forall x . v x <-> v' x) -> (Snk v k a -> Snk v' k a)
mapVSnk b = Snk . dimap (b <~) (mapVSol (~> b)) . runSnk


newtype Sig v k a b = Sig { runSig :: v a -> k b -> Sol v k }

instance (K.Representable k, V.Representable v) => Cat.Category (Sig v k) where
  id = Sig (flip (••))
  Sig f . Sig g = Sig (\ a c -> liftSolWithK (\ go -> g a (inK (go . (`f` c) . inV0))))

instance (Contravariant k, Functor v) => Profunctor (Sig v k) where
  dimap f g = Sig . dimap (fmap f) (lmap (contramap g)) . runSig

instance (Contravariant k, Functor v) => Functor (Sig v k a) where
  fmap = rmap

instance (K.Representable k, V.Representable v) => Applicative (Sig v k a) where
  pure a = Sig (const (•• inV0 a))
  (<*>) = ap

instance (K.Representable k, V.Representable v) => Monad (Sig v k a) where
  Sig m >>= f = Sig (\ a b -> liftSolWithK (\ go -> m a (inK (\ a' -> go (runSig (f a') a b)))))

mapKSig :: (K.Representable k, K.Representable k') => (forall x . k x <-> k' x) -> (Sig v k a b -> Sig v k' a b)
mapKSig b = Sig . fmap (dimap (b <~) (mapKSol (~> b))) . runSig

mapVSig :: (V.Representable v, V.Representable v') => (forall x . v x <-> v' x) -> (Sig v k a b -> Sig v' k a b)
mapVSig b = Sig . dimap (b <~) (rmap (mapVSol (~> b))) . runSig


-- Conversions

solSrc
  :: K.Representable k
  =>      Sol v k
            <->
          Src v k |- Δ
solSrc = Src . const <-> ($ inK absurdΔ) . runSrc


solSnk
  :: V.Representable v
  =>      Sol v k
            <->
     Γ -| Snk v k
solSnk = Snk . const <-> ($ inV (const Γ)) . runSnk


srcSig
  :: V.Representable v
  =>      Src v k |- b
            <->
     Γ -| Sig v k |- b
srcSig = Sig . const . runSrc <-> Src . ($ inV (const Γ)) . runSig

composeSrcSig :: (K.Representable k, V.Representable v) => Src v k a -> Sig v k a b -> Src v k b
composeSrcSig src sig = srcSig <~ (sig <<< src ~> srcSig)


snkSig
  :: K.Representable k
  => a -| Snk v k
            <->
     a -| Sig v k |- Δ
snkSig = Sig . fmap const . runSnk <-> Snk . fmap ($ inK absurdΔ) . runSig

composeSigSnk :: (K.Representable k, V.Representable v) => Sig v k a b -> Snk v k b -> Snk v k a
composeSigSnk sig snk = snkSig <~ (snk ~> snkSig <<< sig)


solSig
  :: (K.Representable k, V.Representable v)
  =>      Sol v k
            <->
     Γ -| Sig v k |- Δ
solSig = Sig . const . const <-> ($ inK absurdΔ) . ($ inV (const Γ)) . runSig


composeSrcSnk :: (K.Representable k, V.Representable v) => Src v k a -> Snk v k a -> Sol v k
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
