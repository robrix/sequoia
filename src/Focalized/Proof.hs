module Focalized.Proof
( runDerivation
, Derivation(..)
) where

runDerivation :: Derivation a -> [a]
runDerivation (Derivation m) = m Nil

type Prop = String
type Context = Snoc Prop

newtype Derivation a = Derivation (Context -> [a])


data Snoc a
  = Nil
  | Snoc a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
