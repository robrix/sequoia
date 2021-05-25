{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Focalized.Proof
( runProof
, Proof(..)
, Entry(..)
, Context
, Name
, pattern Γ
, pattern Γ'
, pattern Δ
, pattern Δ'
, (<|)
, (|>)
, (:|-:)(..)
, contradiction
, assert
, refute
, Prop(..)
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
import           Focalized.B
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


data Entry f a
  = M a
  | J (f a)

type Context f a = B (Entry f a)
type Name = String

pattern Γ, Γ', Δ, Δ' :: Context f Name
pattern Γ = Leaf (M "Γ")
pattern Γ' = Leaf (M "Γ′")
pattern Δ = Leaf (M "Δ")
pattern Δ' = Leaf (M "Δ′")


(<|) :: f a -> Context f a -> Context f a
e <| c = Leaf (J e) <> c

infixr 5 <|

(|>) :: Context f a -> f a -> Context f a
c |> e = c <> Leaf (J e)

infixl 5 |>


data a :|-: b = a :|-: b

infix 2 :|-:


contradiction :: (Alternative f, Alternative g) => f a :|-: g a
contradiction = empty :|-: empty

assert :: Alternative f => g a -> f a :|-: Context g a
assert b = empty :|-: pure (J b)

refute :: Alternative g => f a -> Context f a :|-: g a
refute a = pure (J a) :|-: empty


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


type C p a = S.Multiset (Prop p a)
type L p a = (C p a, p (Prop p a))
type R p a = (p (Prop p a), C p a)

match :: (Alternative m, Monad m, Ord a) => Either (L FOL a :|-: C FOL a) (C FOL a :|-: R FOL a) -> m ()
match = \case
  Left  ((_Γ, p) :|-: _Δ) -> case p of
    Fls      -> pure ()
    Tru      -> empty -- no L rule for truth
    p :/\: q -> _Γ |> p |> q |- _Δ
    p :\/: q -> _Γ |> p |- _Δ >> _Γ |> q |- _Δ
    p :=>: q -> _Γ |- p <| _Δ >> _Γ |> q |- _Δ -- fixme: split _Γ & _Δ (multiplicative nondeterminism)
    Not p    -> _Γ |- p <| _Δ
  Right (_Γ :|-: (p, _Δ)) -> case p of
    Fls      -> empty -- no R rule for falsity
    Tru      -> pure ()
    p :/\: q -> _Γ |- p <| _Δ >> _Γ |- q <| _Δ -- fixme: split _Γ & _Δ (multiplicative nondeterminism)
    p :\/: q -> (_Γ |- p <| _Δ) <|> (_Γ |- q <| _Δ)
    p :=>: q -> _Γ |> p |- q <| _Δ
    Not p    -> _Γ |> p |- _Δ
  where
  (<|) = S.insert
  (|>) = flip S.insert

(|-), chooseL, chooseR  :: (Alternative m, Monad m, Ord a) => C FOL a -> C FOL a -> m ()

_Γ |- _Δ = chooseL _Γ _Δ <|> chooseR _Γ _Δ

chooseL _Γ _Δ = foldMapA (\ (p, _Γ') -> case p of
  V _ -> empty
  P p -> match (Left ((_Γ', p) :|-: _Δ))) (S.quotients _Γ)

chooseR _Γ _Δ = foldMapA (\ (p, _Δ') -> case p of
  V _ -> empty
  P p -> match (Right (_Γ :|-: (p, _Δ')))) (S.quotients _Δ)
