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
, Sequent(..)
, contradiction
, assert
, refute
, Rule(..)
, axiom
, init
, cut
, Prop(..)
, FOL(..)
, flsL
, truR
, conjL
, conjR
, disjL
, disjR1
, disjR2
, implL
, implR
, notL
, notR
) where

import           Control.Carrier.NonDet.Church
import           Control.Carrier.Reader
import           Data.Functor.Identity
import qualified Data.Set as S
import           Focalized.B
import           Prelude hiding (init)

runProof :: Ord b => Γ a -> Proof a b -> Δ b
runProof hyp (Proof m) = run (runNonDetM S.singleton (runReader hyp m))

newtype Proof a b = Proof (ReaderC (Γ a) (NonDetC Identity) b)

type Γ = S.Set
type Δ = S.Set


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


data Sequent f g a = Context f a :|-: Context g a

infix 2 :|-:


contradiction :: Sequent f g a
contradiction = empty :|-: empty

assert :: g a -> Sequent f g a
assert b = empty :|-: pure (J b)

refute :: f a -> Sequent f g a
refute a = pure (J a) :|-: empty


data Rule f g a = [Sequent f g a] :---: Sequent f g a

infix 1 :---:

axiom :: Sequent f g a -> Rule f g a
axiom s = [] :---: s


init :: f Name -> Rule f f Name
init a = axiom $ Γ |> a :|-: a <| Δ

cut :: f Name -> Rule f f Name
cut a =
  [ Γ :|-: a <| Δ, Γ' |> a :|-: Δ' ]
  :---:
  Γ <> Γ' :|-: Δ <> Δ'


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

(\/), (/\), (==>) :: Prop FOL a -> Prop FOL a -> Prop FOL a
p \/ q = P (p :\/: q)
p /\ q = P (p :/\: q)
p ==> q = P (p :=>: q)

infixr 6 ==>
infixr 7 \/
infixr 8 /\

flsL :: Rule (Prop FOL) g Name
flsL = axiom $ Γ |> P Fls :|-: Δ

truR :: Rule f (Prop FOL) Name
truR = axiom $ Γ :|-: P Tru <| Δ

conjL :: Prop FOL Name -> Prop FOL Name -> Rule (Prop FOL) g Name
conjL p q =
  [ Γ |> p |> q :|-: Δ ]
  :---:
  Γ |> p /\ q :|-: Δ

conjR :: Prop FOL Name -> Prop FOL Name -> Rule f (Prop FOL) Name
conjR p q =
  [ Γ :|-: p <| Δ, Γ' :|-: q <| Δ' ]
  :---:
  Γ <> Γ' :|-: p /\ q <| Δ <> Δ'

disjL :: Prop FOL Name -> Prop FOL Name -> Rule (Prop FOL) g Name
disjL p q =
  [ Γ |> p :|-: Δ, Γ |> q :|-: Δ ]
  :---:
  Γ |> p \/ q :|-: Δ

disjR1, disjR2 :: Prop FOL Name -> Prop FOL Name -> Rule f (Prop FOL) Name

disjR1 p q =
  [ Γ :|-: p <| Δ ]
  :---:
  Γ :|-: p \/ q <| Δ

disjR2 p q =
  [ Γ :|-: q <| Δ ]
  :---:
  Γ :|-: p \/ q <| Δ

implL, implR :: Prop FOL Name -> Prop FOL Name -> Rule (Prop FOL) (Prop FOL) Name

implL p q =
  [ Γ :|-: p <| Δ, Γ' |> q :|-: Δ' ]
  :---:
  Γ <> Γ' |> p ==> q :|-: Δ <> Δ'

implR p q =
  [ Γ |> p :|-: q <| Δ ]
  :---:
  Γ :|-: p ==> q <| Δ

notL, notR :: Prop FOL Name -> Rule (Prop FOL) (Prop FOL) Name

notL p =
  [ Γ :|-: p <| Δ ]
  :---:
  Γ |> P (Not p) :|-: Δ

notR p =
  [ Γ |> p :|-: Δ ]
  :---:
  Γ :|-: P (Not p) <| Δ
