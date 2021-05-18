module Focalized.Proof
( runDerivation
, Derivation(..)
) where

import Control.Carrier.NonDet.Church

runDerivation :: Derivation a -> [a]
runDerivation (Derivation m) = runNonDetA m []

type Prop = String
type Context = [Prop]

newtype Derivation a = Derivation (NonDetC ((->) Context) a)
