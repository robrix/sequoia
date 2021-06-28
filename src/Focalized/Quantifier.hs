{-# LANGUAGE ExistentialQuantification #-}
module Focalized.Quantifier
( -- * Universal quantifier
  ForAll(..)
  -- * Existential quantifier
, Exists(..)
, runExists
) where

import Focalized.CPS
import Focalized.Polarity

-- Universal quantifier

newtype ForAll r p f = ForAll { runForAll :: forall x . Polarized p x => r ••f x }

instance Polarized N (ForAll r p f)


-- Universal quantifier

data Exists r p f = forall x . Polarized p x => Exists (r ••f x)

instance Polarized P (Exists r p f)

runExists :: (forall x . Polarized p x => f x -> a) -> Exists r p f -> r ••a
runExists f (Exists r) = K (\ k -> runK r (K (runK k . f)))
