{-# LANGUAGE PatternSynonyms #-}
module Focalized.Proof
( runProof
, Proof(..)
, Entry(..)
, Context(..)
, pattern Γ
, pattern Δ
, (:|-:)(..)
, contradiction
, assert
, refute
, Rule(..)
, axiom
, init
, Prop(..)
, FOL(..)
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


data a :|-: b = Γ a :|-: Δ b

infix 2 :|-:


contradiction :: a :|-: b
contradiction = empty :|-: empty

assert :: b -> a :|-: b
assert b = empty :|-: pure b

refute :: a -> a :|-: b
refute a = pure a :|-: empty


data Rule a b = [a :|-: b] :---: (a :|-: b)

infix 1 :---:

axiom :: a :|-: b -> Rule a b
axiom s = [] :---: s


init :: a -> Rule a a
init a = axiom $ pure a :|-: pure a


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
