{-# LANGUAGE ExistentialQuantification #-}
module Sequoia.Connective.Exists
( -- * Existential quantification
  Exists(..)
, runExists
) where

import Sequoia.Continuation as K
import Sequoia.Functor.K
import Sequoia.Polarity

-- Universal quantification

data Exists r p f = forall x . Polarized p x => Exists (K r **f x)

instance Polarized P (Exists r p f)

runExists :: (forall x . Polarized p x => f x -> a) -> Exists r p f -> K r **a
runExists f (Exists r) = inK (\ k -> r • inK (exK k . f))
