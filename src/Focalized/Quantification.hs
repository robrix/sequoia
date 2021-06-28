{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Quantification
( -- * Universal quantification
  ForAll(..)
  -- * Existential quantification
, Exists(..)
, runExists
  -- * Quantified constraints
, type (==>)
) where

import Data.Kind (Constraint)
import Focalized.CPS
import Focalized.Polarity

-- Universal quantification

newtype ForAll r p f = ForAll { runForAll :: forall x . Polarized p x => r ••f x }

instance Polarized N (ForAll r p f)


-- Universal quantification

data Exists r p f = forall x . Polarized p x => Exists (r ••f x)

instance Polarized P (Exists r p f)

runExists :: (forall x . Polarized p x => f x -> a) -> Exists r p f -> r ••a
runExists f (Exists r) = K (\ k -> runK r (K (runK k . f)))


-- Quantified constraints

type (cx ==> cf) f = (forall x . cx x => cf (f x)) :: Constraint

infix 5 ==>
