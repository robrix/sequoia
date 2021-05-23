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
import           Control.Monad (ap)
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


data FOL a
  = V a
  | Fls
  | Tru
  | FOL a :\/: FOL a
  | FOL a :/\: FOL a
  | Not (FOL a)
  | FOL a :=>: FOL a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 :=>:
infixr 7 :\/:
infixr 8 :/\:

instance Applicative FOL where
  pure = V

  (<*>) = ap

instance Monad FOL where
  p >>= f = case p of
    V a      -> f a
    Fls      -> Fls
    Tru      -> Tru
    p :\/: q -> (p >>= f) :\/: (q >>= f)
    p :/\: q -> (p >>= f) :/\: (q >>= f)
    Not p    -> Not (p >>= f)
    p :=>: q -> (p >>= f) :=>: (q >>= f)

(\/), (/\), (==>) :: FOL a -> FOL a -> FOL a
(\/) = (:\/:)
(/\) = (:/\:)
(==>) = (:=>:)

infixr 6 ==>
infixr 7 \/
infixr 8 /\

flsL :: Rule FOL g Name
flsL = axiom $ Γ |> Fls :|-: Δ

truR :: Rule f FOL Name
truR = axiom $ Γ :|-: Tru <| Δ

conjL :: FOL Name -> FOL Name -> Rule FOL g Name
conjL p q =
  [ Γ |> p |> q :|-: Δ ]
  :---:
  Γ |> p /\ q :|-: Δ

conjR :: FOL Name -> FOL Name -> Rule f FOL Name
conjR p q =
  [ Γ :|-: p <| Δ, Γ' :|-: q <| Δ' ]
  :---:
  Γ <> Γ' :|-: p /\ q <| Δ <> Δ'

disjL :: FOL Name -> FOL Name -> Rule FOL g Name
disjL p q =
  [ Γ |> p :|-: Δ, Γ |> q :|-: Δ ]
  :---:
  Γ |> p \/ q :|-: Δ

disjR1, disjR2 :: FOL Name -> FOL Name -> Rule f FOL Name

disjR1 p q =
  [ Γ :|-: p <| Δ ]
  :---:
  Γ :|-: p \/ q <| Δ

disjR2 p q =
  [ Γ :|-: q <| Δ ]
  :---:
  Γ :|-: p \/ q <| Δ

implL, implR :: FOL Name -> FOL Name -> Rule FOL FOL Name

implL p q =
  [ Γ :|-: p <| Δ, Γ' |> q :|-: Δ' ]
  :---:
  Γ <> Γ' |> p ==> q :|-: Δ <> Δ'

implR p q =
  [ Γ |> p :|-: q <| Δ ]
  :---:
  Γ :|-: p ==> q <| Δ

notL, notR :: FOL Name -> Rule FOL FOL Name

notL p =
  [ Γ :|-: p <| Δ ]
  :---:
  Γ |> Not p :|-: Δ

notR p =
  [ Γ |> p :|-: Δ ]
  :---:
  Γ :|-: Not p <| Δ
