module Focalized.Proof
( Derivation(..)
) where

import Control.Carrier.NonDet.Church
import Data.Functor.Identity

newtype Derivation a = Derivation (NonDetC Identity a)
