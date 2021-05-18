module Focalized.Proof
( runDerivation
, Derivation(..)
) where

import Control.Carrier.NonDet.Church

runDerivation :: Derivation a -> [a]
runDerivation (Derivation m) = runNonDetA m Nil

type Prop = String
type Context = Snoc Prop

newtype Derivation a = Derivation (NonDetC ((->) Context) a)


data Snoc a
  = Nil
  | Snoc a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
