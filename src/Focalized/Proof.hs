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

import           Control.Carrier.NonDet.Church
import           Control.Carrier.Reader
import qualified Control.Category as C
import           Data.Functor.Identity
import qualified Data.Sequence as S
import           Prelude hiding (init)

runProof :: Γ a -> Proof a b -> Δ b
runProof hyp (Proof m) = run (runNonDetA (runReader hyp m))

newtype Proof a b = Proof (ReaderC (Γ a) (NonDetC Identity) b)

instance C.Category Proof where
  id = Proof (ReaderC oneOf)
  Proof bc . ab = Proof $ ReaderC $ \ h -> runReader (runProof h ab) bc

type Γ = S.Seq
type Δ = S.Seq


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
