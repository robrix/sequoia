{-# LANGUAGE ExistentialQuantification #-}
module Focalized.Connective.Exists
( -- * Existential quantification
  Exists(..)
, runExists
) where

import Focalized.Continuation
import Focalized.Polarity

-- Universal quantification

data Exists k p f = forall x . Polarized p x => Exists (k (k (f x)))

instance Polarized P (Exists r p f)

runExists :: Representable k => (forall x . Polarized p x => f x -> a) -> Exists k p f -> k (k a)
runExists f (Exists r) = inK (\ k -> exK r (inK (exK k . f)))
