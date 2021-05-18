module Focalized.Proof
( runDerivation
, Derivation(..)
, (:|-:)(..)
, contradiction
, assert
, refute
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

instance Semigroup (Snoc a) where
  as <> Nil       = as
  as <> (bs :> b) = (as <> bs) :> b

instance Monoid (Snoc a) where
  mempty = Nil

instance Applicative Snoc where
  pure a = Nil :> a
  Nil     <*> _  = Nil
  fs :> f <*> as = (fs <*> as) <> (f <$> as)

instance Monad Snoc where
  Nil     >>= _ = Nil
  as :> a >>= f = (as >>= f) <> f a


data a :|-: b = Γ a :|-: Δ b

infix 1 :|-:


contradiction :: a :|-: b
contradiction = Nil :|-: []

assert :: b -> a :|-: b
assert b = Nil :|-: [b]

refute :: a -> a :|-: b
refute a = Nil :> a :|-: []
