module Focalized.Proof
( runProof
, Proof(..)
, (:|-:)(..)
, contradiction
, assert
, refute
, Rule(..)
, axiom
, init
) where

import qualified Control.Category as C
import           Data.Sequence
import           Prelude hiding (init)

runProof :: Proof a b -> Seq b
runProof (Proof m) = m empty

newtype Proof a b = Proof (Γ a |- Δ b)

instance C.Category Proof where
  id = Proof id
  Proof bc . Proof ab = Proof $ bc . ab

type Γ = Seq
type Δ = Seq
type (|-) = (->)


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
