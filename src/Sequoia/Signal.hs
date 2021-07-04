{-# LANGUAGE TypeFamilies #-}
module Sequoia.Signal
( -- * Signals
  Sol(..)
, Src(..)
, Snk(..)
, Sig(..)
, srcSig
, snkSig
, type (<->)
, inB
, exBl
, exBr
) where

import Sequoia.Calculus.Context
import Sequoia.Continuation

-- Signals

newtype Sol k     = Sol { runSol :: k Δ }
newtype Src k   b = Src { runSrc :: k **b }
newtype Snk k a   = Snk { runSnk ::        k a }
newtype Sig k a b = Sig { runSig :: k b -> k a }


srcSig
  :: Representable k
  =>      Src k |- b
           <->
     Γ -| Sig k |- b
srcSig = inB srcToSig sigToSrc
  where
  srcToSig (Src src) = Sig (inK1 (const . exK src . inK))
  sigToSrc (Sig sig) = Src (inK ((`exK` Γ) . sig))


snkSig
  :: Representable k
  => a -| Snk k
           <->
     a -| Sig k |- Δ
snkSig = inB snkToSig sigToSnk
  where
  snkToSig (Snk snk) = Sig (inK1 (const (exK snk)))
  sigToSnk (Sig sig) = Snk (inK (exK (sig (inK absurdΔ))))

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

inB :: (a -> b) -> (b -> a) -> a <-> b
inB l r f = f l r

exBl :: a <-> b -> (a -> b)
exBl f = f const

exBr :: a <-> b -> (b -> a)
exBr f = f (const id)
