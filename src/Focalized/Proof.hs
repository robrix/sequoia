module Focalized.Proof
( runProof
, Proof(..)
, Entry(..)
, (:|-:)(..)
, contradiction
, assert
, refute
, Rule(..)
, axiom
, init
, Prop(..)
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


data Prop a
  = Var a
  | Fls
  | Tru
  | Prop a :\/: Prop a
  | Prop a :/\: Prop a
  | Not (Prop a)
  | Prop a :=>: Prop a

infixr 6 :=>:
infixr 7 :\/:
infixr 8 :/\:
