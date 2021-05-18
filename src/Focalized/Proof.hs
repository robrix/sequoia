module Focalized.Proof
( runProof
, Proof(..)
, (:|-:)(..)
, contradiction
, assert
, refute
, init
) where

import Control.Applicative (Alternative(..))
import Prelude hiding (init)

runProof :: Proof a b -> [b]
runProof (Proof m) = m Nil

newtype Proof a b = Proof (Γ a |- Δ b)

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

instance Alternative Snoc where
  empty = mempty
  (<|>) = (<>)

instance Monad Snoc where
  Nil     >>= _ = Nil
  as :> a >>= f = (as >>= f) <> f a


data a :|-: b = Γ a :|-: Δ b

infix 1 :|-:


contradiction :: a :|-: b
contradiction = empty :|-: empty

assert :: b -> a :|-: b
assert b = empty :|-: pure b

refute :: a -> a :|-: b
refute a = pure a :|-: empty


init :: a -> a :|-: a
init a = pure a :|-: pure a
