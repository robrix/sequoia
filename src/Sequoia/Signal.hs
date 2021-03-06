{-# LANGUAGE TypeFamilies #-}
module Sequoia.Signal
( -- * Signals
  _Sig
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
import           Fresnel.Getter
import           Fresnel.Iso
import           Fresnel.Review
import           Sequoia.Calculus.Context
import           Sequoia.Functor.Sink
import           Sequoia.Functor.Source
import           Sequoia.Monad.Run
import           Sequoia.Profunctor.Command
import           Sequoia.Profunctor.Continuation as K
import           Sequoia.Profunctor.Value as V

-- Signals

_Sig :: Iso (Sig e r a b) (Sig e' r' a' b') (b • r -> e ∘ a -> e |- r) (b' • r' -> e' ∘ a' -> e' |- r')
_Sig = coerced

newtype Sig e r a b = Sig { runSig :: b • r -> e ∘ a -> e |- r }

instance Cat.Category (Sig e r) where
  id = Sig (↓↑)
  Sig f . Sig g = Sig (\ c a -> cont (\ _K -> g (_K (f c . pure)) a))

instance Profunctor (Sig e r) where
  dimap f g = Sig . dimap (lmap g) (lmap (fmap f)) . runSig

instance Functor (Sig e r a) where
  fmap = rmap

instance Applicative (Sig e r a) where
  pure a = Sig (ckv (const a))
  (<*>) = ap

instance Monad (Sig e r a) where
  Sig m >>= f = Sig (\ b a -> cont (\ _K -> m (_K (\ a' -> runSig (f a') b a)) a))

mapKSig :: Iso' r r' -> (Sig e r a b -> Sig e r' a b)
mapKSig b = withIso b $ \ to from -> Sig . dimap (rmap from) (rmap (rmap to)) . runSig

mapVSig :: Iso' e e' -> (Sig e r a b -> Sig e' r a b)
mapVSig b = withIso b $ \ to from -> Sig . rmap (dimap (lmap to) (lmap from)) . runSig


-- Conversions

solSrc
  :: Iso'
     (     e |- r     )
  -- ------------------
     (    Src  e r ⊢ r)
solSrc = iso (src . const) (($ idK) . runSrc)


solSnk
  :: Iso'
     (     e |- r     )
  -- ------------------
     (e ⊣ Snk  e r    )
solSnk = iso (snk . const) (($ idV) . runSnk)


srcSig
  :: Iso'
     (    Src  e r ⊢ b)
  -- ------------------
     (e ⊣ Sig  e r ⊢ b)
srcSig = _Src.from (_Sig.rmapping (constantWith idV (<<∘)))

composeSrcSig :: Src e r a -> Sig e r a b -> Src e r b
composeSrcSig src sig = review srcSig (sig <<< view srcSig src)


snkSig
  :: Iso'
     (a ⊣ Snk  e r    )
  -- ------------------
     (a ⊣ Sig  e r ⊢ r)
snkSig = _Snk.from (_Sig.constantWith idK (flip ((.) . (•<<))))

composeSigSnk :: Sig e r a b -> Snk e r b -> Snk e r a
composeSigSnk sig snk = review snkSig (view snkSig snk <<< sig)


solSig
  :: Iso'
     (     e |- r     )
  -- ------------------
     (e ⊣ Sig  e r ⊢ r)
solSig = iso (Sig . const . const) (($ idV) . ($ idK) . runSig)


composeSrcSnk :: Src e r a -> Snk e r a -> e |- r
composeSrcSnk src snk = review solSig (snk^.snkSig <<< view srcSig src)


{-
       o
  ==> ---> Src
   │        │
 i │        │ i
   ↓        ↓
  Snk ---> Sig
       o
-}
