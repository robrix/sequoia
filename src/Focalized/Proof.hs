module Focalized.Proof
( runDerivation
, Derivation(..)
) where

import Control.Carrier.NonDet.Church
import Data.Functor.Identity

runDerivation :: Derivation a -> [a]
runDerivation (Derivation m) = run (runNonDetA m)

newtype Derivation a = Derivation (NonDetC Identity a)
