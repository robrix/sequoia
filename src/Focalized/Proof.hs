module Focalized.Proof
( runProof
, Proof(..)
, (<|)
, (|>)
, (:|-:)(..)
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

infix 4 |-


(<|) :: Ord a => a -> S.Multiset a -> S.Multiset a
(<|) = S.insert

infixr 5 <|

(|>) :: Ord a => S.Multiset a -> a -> S.Multiset a
(|>) = flip S.insert

infixl 5 |>


data a :|-: b = a :|-: b

infix 2 :|-:
