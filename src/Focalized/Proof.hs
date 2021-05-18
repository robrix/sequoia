module Focalized.Proof
( runDerivation
, Derivation(..)
, (:|-:)(..)
) where

runDerivation :: Derivation a b -> [b]
runDerivation (Derivation m) = m Nil

newtype Derivation a b = Derivation (Γ a |- Δ b)

type Γ = Snoc
type Δ = []
type (|-) = (->)

data Snoc a
  = Nil
  | Snoc a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :>


data a :|-: b = Γ a :|-: Δ b

infix 1 :|-:
