{-# LANGUAGE ExistentialQuantification #-}
module Sequoia.Connective.Exists
( -- * Existential quantification
  Exists(..)
, runExists
) where

import Sequoia.Functor.Continuation as K
import Sequoia.Functor.K
import Sequoia.Polarity

-- Universal quantification

data Exists r p f = forall x . Polarized p x => Exists (K r (K r (f x)))

instance Polarized P (Exists r p f)

runExists :: (forall x . Polarized p x => f x -> a) -> Exists r p f -> K r (K r a)
runExists f (Exists r) = K (\ k -> r • K (runK k . f))
