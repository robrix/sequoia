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
, (|-)
) where

import           Control.Carrier.NonDet.Church
import           Control.Carrier.Reader
import           Data.Either (partitionEithers)
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
  decompose :: (Alternative m, Monad m, Ord a) => Γ (l a) :|-: Δ (r a) -> Either (l a) (r a) -> m ()

  decomposeL :: (Alternative m, Monad m, Ord a) => l a -> Γ (l a) :|-: Δ (r a) -> m ()
  decomposeL l c = decompose c (Left l)

  decomposeR :: (Alternative m, Monad m, Ord a) => Γ (l a) :|-: Δ (r a) -> r a -> m ()
  decomposeR c = decompose c . Right

  unJudgementL :: l a -> Either a (l a)
  unJudgementR :: r a -> Either a (r a)


(|-) :: (Alternative m, Monad m, Judgement r l, Ord a, Ord (r a), Ord (l a)) => Γ (l a) -> Δ (r a) -> m ()
_Γ |- _Δ = case (qΓ, qΔ) of
  ([], []) -> foldMapA (guard . (`elem` aΓ)) aΔ
  _        -> foldMapA (\ (p, _Γ') -> decomposeL p (_Γ' :|-: _Δ)) qΓ
          <|> foldMapA (\ (p, _Δ') -> decomposeR (_Γ :|-: _Δ') p) qΔ
  where
  (aΓ, qΓ) = partitionEithers [ (, _Γ') <$> unJudgementL p | (p, _Γ') <- S.quotients _Γ ]
  (aΔ, qΔ) = partitionEithers [ (, _Δ') <$> unJudgementR p | (p, _Δ') <- S.quotients _Δ ]

infix 4 |-
