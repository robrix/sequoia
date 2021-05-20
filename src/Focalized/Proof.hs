{-# LANGUAGE PatternSynonyms #-}
module Focalized.Proof
( runProof
, Proof(..)
, Entry(..)
, Context(..)
, pattern Γ
, pattern Δ
, (<|)
, viewl
, (|>)
, viewr
, Sequent(..)
, contradiction
, assert
, refute
, Rule(..)
, axiom
, init
, Prop(..)
, FOL(..)
, flsL
, truR
) where

import           Control.Carrier.NonDet.Church
import           Control.Carrier.Reader
import           Data.Functor.Identity
import qualified Data.Sequence as S
import           Prelude hiding (init)

runProof :: Γ a -> Proof a b -> Δ b
runProof hyp (Proof m) = run (runNonDetA (runReader hyp m))

newtype Proof a b = Proof (ReaderC (Γ a) (NonDetC Identity) b)

type Γ = S.Seq
type Δ = S.Seq


data Entry f a
  = M a
  | J (f a)

data Context f a
  = C (Entry f a)
  | Context f a :<>: Context f a

infixr 5 :<>:

pattern Γ, Δ :: Context f String
pattern Γ = C (M "Γ")
pattern Δ = C (M "Δ")


(<|) :: f a -> Context f a -> Context f a
e <| c = C (J e) :<>: c

infixr 5 <|

viewl :: Context f a -> (Entry f a, Maybe (Context f a))
viewl = \case
  C e      -> (e, Nothing)
  l :<>: r -> go l r where
    go l r = case l of
      C e        -> (e, Just r)
      l1 :<>: l2 -> go l1 (l2 :<>: r)

(|>) :: Context f a -> f a -> Context f a
c |> e = c :<>: C (J e)

infixl 5 |>

viewr :: Context f a -> (Maybe (Context f a), Entry f a)
viewr = \case
  C e -> (Nothing, e)
  l :<>: r -> go l r where
    go l = \case
      C e        -> (Just l, e)
      r1 :<>: r2 -> go (l :<>: r1) r2


data Sequent f g a = Maybe (Context f a) :|-: Maybe (Context g a)

infix 2 :|-:


contradiction :: Sequent f g a
contradiction = empty :|-: empty

assert :: g a -> Sequent f g a
assert b = empty :|-: pure (C (J b))

refute :: f a -> Sequent f g a
refute a = pure (C (J a)) :|-: empty


data Rule f g a = [Sequent f g a] :---: (Sequent f g a)

infix 1 :---:

axiom :: Sequent f g a -> Rule f g a
axiom s = [] :---: s


init :: f a -> Rule f f a
init a = axiom $ pure (C (J a)) :|-: pure (C (J a))


data Prop f a
  = V a
  | P (f (Prop f a))

data FOL a
  = Fls
  | Tru
  | a :\/: a
  | a :/\: a
  | Not a
  | a :=>: a

infixr 6 :=>:
infixr 7 :\/:
infixr 8 :/\:

flsL :: Rule (Prop FOL) g String
flsL = axiom $ Just (Γ |> P Fls) :|-: Just Δ

truR :: Rule f (Prop FOL) String
truR = axiom $ Just Γ :|-: Just (P Tru <| Δ)
