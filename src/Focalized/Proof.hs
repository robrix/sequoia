{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Focalized.Proof
( runProof
, Proof(..)
, (<|)
, (|>)
, (:|-:)(..)
, Prop(..)
, unProp
, connective
, FOL(..)
, tru
, fls
, (==>)
, (\/)
, (/\)
, neg
, match
, (|-)
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


unProp :: Prop p a -> Either a (p (Prop p a))
unProp = \case
  V a -> Left a
  P p -> Right p

connective :: Alternative m => Prop p a -> m (p (Prop p a))
connective = either (const empty) pure . unProp


data FOL a
  = Fls
  | Tru
  | a :\/: a
  | a :/\: a
  | Not a
  | a :=>: a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 :=>:
infixr 7 :\/:
infixr 8 :/\:


tru, fls :: Prop FOL a

tru = P Tru
fls = P Fls

(==>), (\/), (/\) :: Prop FOL a -> Prop FOL a -> Prop FOL a

p ==> q = P (p :=>: q)
p \/ q = P (p :\/: q)
p /\ q = P (p :/\: q)

infixr 6 ==>
infixr 7 \/
infixr 8 /\

neg :: Prop FOL a -> Prop FOL a
neg p = P (Not p)


type Context p a = S.Multiset (Prop p a)

match :: (Alternative m, Monad m, Ord a) => Either ((Context FOL a, FOL (Prop FOL a)) :|-: Context FOL a) (Context FOL a :|-: (FOL (Prop FOL a), Context FOL a)) -> m ()
match = \case
  Left  ((_Γ, p) :|-: _Δ) -> case p of
    Fls      -> pure ()
    Tru      -> empty -- no L rule for truth
    p :/\: q -> p <| q <| _Γ |- _Δ
    p :\/: q -> p <| _Γ |- _Δ >> q <| _Γ |- _Δ
    p :=>: q -> _Γ |- _Δ |> p >> q <| _Γ |- _Δ -- fixme: split _Γ & _Δ (multiplicative nondeterminism)
    Not p    -> _Γ |- _Δ |> p
  Right (_Γ :|-: (p, _Δ)) -> case p of
    Fls      -> empty -- no R rule for falsity
    Tru      -> pure ()
    p :/\: q -> _Γ |- _Δ |> p >> _Γ |- _Δ |> q -- fixme: split _Γ & _Δ (multiplicative nondeterminism)
    p :\/: q -> (_Γ |- _Δ |> p) <|> (_Γ |- _Δ |> q)
    p :=>: q -> p <| _Γ |- _Δ |> q
    Not p    -> p <| _Γ |- _Δ

(|-), chooseL, chooseR  :: (Alternative m, Monad m, Ord a) => Context FOL a -> Context FOL a -> m ()

_Γ |- _Δ = chooseL _Γ _Δ <|> chooseR _Γ _Δ

chooseL _Γ _Δ = foldMapA (\ (p, _Γ') -> case p of
  V _ -> empty
  P p -> match (Left ((_Γ', p) :|-: _Δ))) (S.quotients _Γ)

chooseR _Γ _Δ = foldMapA (\ (p, _Δ') -> case p of
  V _ -> empty
  P p -> match (Right (_Γ :|-: (p, _Δ')))) (S.quotients _Δ)
