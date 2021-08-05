{-# LANGUAGE ExistentialQuantification #-}
module Sequoia.Connective.Exists
( -- * Existential quantification
  Exists(..)
, runExists
) where

import Sequoia.Polarity
import Sequoia.Profunctor
import Sequoia.Profunctor.Continuation

-- Universal quantification

data Exists r p f = forall x . Polarized p x => Exists (f x •• r)

instance Polarized P (Exists r p f)

runExists :: (forall x . Polarized p x => f x -> a) -> Exists r p f -> a •• r
runExists f (Exists r) = r <<^ (<<^ f)
