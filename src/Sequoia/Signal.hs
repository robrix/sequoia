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
, type (<->)
, (<->)
, exBl
, exBr
  -- Self-adjunction
, Self(..)
) where

import Data.Distributive
import Data.Functor.Contravariant.Adjunction
import Sequoia.Calculus.Context
import Sequoia.Continuation

-- Signals

newtype Sol k     = Sol { runSol :: k Δ -> k Γ }
newtype Src k   b = Src { runSrc :: k **b }
newtype Snk k a   = Snk { runSnk :: a -> k **Δ }
newtype Sig k a b = Sig { runSig :: k b -> k a }


solSrc
  :: Representable k
  =>      Sol k
           <->
          Src k |- Δ
solSrc = solToSrc <-> srcToSol
  where
  solToSrc (Sol sol) = Src (inK ((`exK` Γ) . sol))
  srcToSol (Src src) = Sol (inK1 (const . exK src . inK))


solSnk
  :: Representable k
  =>      Sol k
           <->
     Γ -| Snk k
solSnk = solToSnk <-> snkToSol
  where
  solToSnk (Sol sol) = Snk (inK . (. sol) . flip exK)
  snkToSol (Snk snk) = Sol (inK . (. snk) . flip exK)


srcSig
  :: Representable k
  =>      Src k |- b
           <->
     Γ -| Sig k |- b
srcSig = srcToSig <-> sigToSrc
  where
  srcToSig (Src src) = Sig (inK1 (const . exK src . inK))
  sigToSrc (Sig sig) = Src (inK ((`exK` Γ) . sig))


snkSig
  :: Representable k
  => a -| Snk k
           <->
     a -| Sig k |- Δ
snkSig = snkToSig <-> sigToSnk
  where
  snkToSig (Snk snk) = Sig (inK . (. snk) . flip exK)
  sigToSnk (Sig sig) = Snk (inK . (. sig) . flip exK)


solSig
  ::      Sol k
           <->
     Γ -| Sig k |- Δ
solSig = (\ (Sol sol) -> Sig sol) <-> (\ (Sig sig) -> Sol sig)


{-
       o
  Sol ---> Src
   │        │
 i │        │ i
   ↓        ↓
  Snk ---> Sig
       o
-}


type a <-> b = forall r . ((a -> b) -> (b -> a) -> r) -> r

infix 1 <->

(<->) :: (a -> b) -> (b -> a) -> a <-> b
(l <-> r) f = f l r

exBl :: a <-> b -> (a -> b)
exBl f = f const

exBr :: a <-> b -> (b -> a)
exBr f = f (const id)


instance Contravariant k => Functor (Src k) where
  fmap f = Src . contramap (contramap f) . runSrc

instance Representable k => Applicative (Src k) where
  pure a = Src (inK (`exK` a))
  Src f <*> Src a = Src (inK (\ b -> exK f (inK (exK a . inK . (exK b .)))))

instance Representable k => Monad (Src k) where
  Src m >>= f = Src (m •<< inK . \ k -> (`exK` k) . runSrc . f)


-- Self-adjunction

newtype Self k a = Self { getSelf :: k a }
  deriving (Contravariant, Functor, Representable)

instance Distributive k => Distributive (Self k) where
  distribute = Self . distribute . fmap getSelf

instance Representable k => Adjunction (Self k) (Self k) where
  leftAdjunct  = fmap inK . (. flip exK) . flip (.)
  rightAdjunct = fmap inK . (. flip exK) . flip (.)
