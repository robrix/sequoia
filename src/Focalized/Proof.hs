{-# LANGUAGE QuantifiedConstraints #-}
module Focalized.Proof
( runProof
, Proof(..)
, (<|)
, (|>)
, (:|-:)(..)
, Prop(..)
, getProp
, connective
, Context
) where

import           Control.Carrier.NonDet.Church
import           Control.Carrier.Reader
import           Data.Functor.Identity
import qualified Focalized.Multiset as S
import           Prelude hiding (init)

runProof :: Ord b => Γ a -> Proof a b -> S.Multiset b
runProof hyp (Proof m) = run (runNonDetM S.singleton (m hyp))

newtype Proof a b = Proof (Γ a |- Δ b)
  deriving (Alternative, Applicative, Functor, Monad) via ReaderC (Γ a) Δ

type Γ = S.Multiset
type Δ = NonDetC Identity
type (|-) = (->)

infix 2 |-


(<|) :: Ord a => a -> S.Multiset a -> S.Multiset a
(<|) = S.insert

infixr 5 <|

(|>) :: Ord a => S.Multiset a -> a -> S.Multiset a
(|>) = flip S.insert

infixl 5 |>


data a :|-: b = a :|-: b

infix 2 :|-:


data Prop f a
  = V a
  | P (f (Prop f a))
  deriving (Foldable, Functor, Traversable)

instance Functor f => Applicative (Prop f) where
  pure = V

  V f <*> a = f <$> a
  P f <*> a = P ((<*> a) <$> f)

instance Functor f => Monad (Prop f) where
  V a >>= f = f a
  P a >>= f = P ((>>= f) <$> a)

deriving instance (forall x . Eq x => Eq (f x), Eq a) => Eq (Prop f a)
deriving instance (forall x . Eq x => Eq (f x), forall x . Ord x => Ord (f x), Ord a) => Ord (Prop f a)
deriving instance (forall x . Show x => Show (f x), Show a) => Show (Prop f a)


getProp :: Prop p a -> Either a (p (Prop p a))
getProp = \case
  V a -> Left a
  P p -> Right p

connective :: Alternative m => Prop p a -> m (p (Prop p a))
connective = either (const empty) pure . getProp


type Context p a = S.Multiset (Prop p a)
