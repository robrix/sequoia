module Focalized.Proof
( runDerivation
, Derivation(..)
) where

runDerivation :: Derivation a b -> [b]
runDerivation (Derivation m) = m Nil

type Context = Snoc

newtype Derivation a b = Derivation (Context a -> [b])


data Snoc a
  = Nil
  | Snoc a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
