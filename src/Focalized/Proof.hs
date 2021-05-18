module Focalized.Proof
( runDerivation
, Derivation(..)
) where

runDerivation :: Derivation a b -> [b]
runDerivation (Derivation m) = m Nil

newtype Derivation a b = Derivation (Γ a |- Δ b)

type Γ = Context
type Δ = []
type (|-) = (->)

data Context a
  = Nil
  | Context a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
