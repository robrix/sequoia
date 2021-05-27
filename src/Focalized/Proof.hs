{-# LANGUAGE FunctionalDependencies #-}
module Focalized.Proof
( runProof
, Proof(..)
, (<|)
, (|>)
, (:|-:)(..)
, type Γ
, type Δ
, Judgement(..)
) where

import           Control.Carrier.NonDet.Church
import           Control.Carrier.Reader
import           Data.Functor.Identity
import qualified Focalized.Multiset as S
import           Prelude hiding (init)

runProof :: Ord b => S.Multiset a -> Proof a b -> S.Multiset b
runProof hyp (Proof m) = run (runNonDetM S.singleton (m hyp))

newtype Proof a b = Proof (S.Multiset a -> NonDetC Identity b)
  deriving (Alternative, Applicative, Functor, Monad) via ReaderC (S.Multiset a) (NonDetC Identity)


(<|) :: Ord a => a -> S.Multiset a -> S.Multiset a
(<|) = S.insert

infixr 5 <|

(|>) :: Ord a => S.Multiset a -> a -> S.Multiset a
(|>) = flip S.insert

infixl 5 |>


data a :|-: b = a :|-: b

infix 4 :|-:


type Γ = S.Multiset
type Δ = S.Multiset

class Judgement r l | r -> l, l -> r where
  decomposeL :: (Alternative m, Monad m, Ord a) => l a -> Γ (l a) :|-: Δ (r a) -> m ()
  decomposeR :: (Alternative m, Monad m, Ord a) => Γ (l a) :|-: Δ (r a) -> r a -> m ()
