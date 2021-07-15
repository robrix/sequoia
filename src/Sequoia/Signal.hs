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

sol :: (K.Representable k, V.Representable v) => (V.Rep v -> K.Rep k) -> Sol k v
sol f = Sol (inV (inK . const . f))

(••) :: (K.Representable k, V.Representable v) => k a -> v a -> Sol k v
k •• a = sol (\ e -> k • e ∘ a)

infix 7 ••

withEnv :: (K.Representable k, V.Representable v) => (V.Rep v -> Sol k v) -> Sol k v
withEnv f = sol (evalSol =<< f)

liftSolWithK :: (K.Representable k, V.Representable v) => ((Sol k v -> K.Rep k) -> Sol k v) -> Sol k v
liftSolWithK f = withEnv (f . flip evalSol)


evalSol :: (K.Representable k, V.Representable v) => Sol k v -> (V.Rep v -> K.Rep k)
evalSol (Sol r) e = e ∘ r • ()


newtype Sol k v     = Sol { runSol :: forall x . v (k x) }

mapKSol :: Functor v => (forall x . k x -> k' x) -> (Sol k v -> Sol k' v)
mapKSol f (Sol r) = Sol (f <$> r)

mapVSol :: (forall x . v x -> v' x) -> (Sol k v -> Sol k v')
mapVSol f (Sol r) = Sol (f r)


newtype Src k v   b = Src { runSrc :: k b -> Sol k v }

instance Contravariant k => Functor (Src k v) where
  fmap f (Src r) = Src (lmap (contramap f) r)

mapKSrc :: Functor v => (forall x . k x <-> k' x) -> (Src k v b -> Src k' v b)
mapKSrc b = Src . dimap (b <~) (mapKSol (~> b)) . runSrc

mapVSrc :: (forall x . v x -> v' x) -> (Src k v b -> Src k v' b)
mapVSrc f = Src . rmap (mapVSol f) . runSrc


newtype Snk k v a   = Snk { runSnk :: v a -> Sol k v }

instance Functor v => Contravariant (Snk k v) where
  contramap f = Snk . lmap (fmap f) . runSnk

mapKSnk :: Functor v => (forall x . k x -> k' x) -> (Snk k v a -> Snk k' v a)
mapKSnk f = Snk . fmap (mapKSol f) . runSnk

mapVSnk :: (forall x . v x <-> v' x) -> (Snk k v a -> Snk k v' a)
mapVSnk b = Snk . dimap (b <~) (mapVSol (~> b)) . runSnk


newtype Sig k v a b = Sig { runSig :: v a -> k b -> Sol k v }

instance (K.Representable k, V.Representable v) => Cat.Category (Sig k v) where
  id = Sig (flip (••))
  Sig f . Sig g = Sig (\ a c -> liftSolWithK (\ go -> g a (inK (go . (`f` c) . inV0))))

instance (Contravariant k, Functor v) => Profunctor (Sig k v) where
  dimap f g = Sig . dimap (fmap f) (lmap (contramap g)) . runSig

instance (Contravariant k, Functor v) => Functor (Sig k v a) where
  fmap = rmap

instance (K.Representable k, V.Representable v) => Applicative (Sig k v a) where
  pure a = Sig (const (•• inV0 a))
  (<*>) = ap

instance (K.Representable k, V.Representable v) => Monad (Sig k v a) where
  Sig m >>= f = Sig (\ a b -> liftSolWithK (\ go -> m a (inK (\ a' -> go (runSig (f a') a b)))))

mapKSig :: Functor v => (forall x . k x <-> k' x) -> (Sig k v a b -> Sig k' v a b)
mapKSig b = Sig . fmap (dimap (b <~) (mapKSol (~> b))) . runSig

mapVSig :: (forall x . v x <-> v' x) -> (Sig k v a b -> Sig k v' a b)
mapVSig b = Sig . dimap (b <~) (rmap (mapVSol (~> b))) . runSig


-- Conversions

solSrc
  :: K.Representable k
  =>      Sol k v
            <->
          Src k v |- Δ
solSrc = Src . const <-> ($ inK absurdΔ) . runSrc


solSnk
  :: V.Representable v
  =>      Sol k v
            <->
     Γ -| Snk k v
solSnk = Snk . const <-> ($ inV (const Γ)) . runSnk


srcSig
  :: V.Representable v
  =>      Src k v |- b
            <->
     Γ -| Sig k v |- b
srcSig = Sig . const . runSrc <-> Src . ($ inV (const Γ)) . runSig

composeSrcSig :: (K.Representable k, V.Representable v) => Src k v a -> Sig k v a b -> Src k v b
composeSrcSig src sig = srcSig <~ (sig <<< src ~> srcSig)


snkSig
  :: K.Representable k
  => a -| Snk k v
            <->
     a -| Sig k v |- Δ
snkSig = Sig . fmap const . runSnk <-> Snk . fmap ($ inK absurdΔ) . runSig

composeSigSnk :: (K.Representable k, V.Representable v) => Sig k v a b -> Snk k v b -> Snk k v a
composeSigSnk sig snk = snkSig <~ (snk ~> snkSig <<< sig)


solSig
  :: (K.Representable k, V.Representable v)
  =>      Sol k v
            <->
     Γ -| Sig k v |- Δ
solSig = Sig . const . const <-> ($ inK absurdΔ) . ($ inV (const Γ)) . runSig


composeSrcSnk :: (K.Representable k, V.Representable v) => Src k v a -> Snk k v a -> Sol k v
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
