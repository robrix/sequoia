module Focalized.Proof
( runProof
, Proof(..)
, (<|)
, (|>)
, (:|-:)(..)
, type Γ
, type Δ
, Prop(..)
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

class Prop p where
  decompose :: (Alternative m, Monad m, Ord a) => Γ (p a) :|-: Δ (p a) -> Either (p a) (p a) -> m ()

  unProp :: p a -> Either a (p a)


(|-) :: (Alternative m, Monad m, Prop p, Ord a, Ord (p a)) => Γ (p a) -> Δ (p a) -> m ()
_Γ |- _Δ = case (qΓ, qΔ) of
  ([], []) -> foldMapA (guard . (`elem` aΓ)) aΔ
  _        -> foldMapA (\ (p, _Γ') -> decompose (_Γ' :|-: _Δ) (Left  p)) qΓ
          <|> foldMapA (\ (p, _Δ') -> decompose (_Γ :|-: _Δ') (Right p)) qΔ
  where
  (aΓ, qΓ) = partitionEithers [ (, _Γ') <$> unProp p | (p, _Γ') <- S.quotients _Γ ]
  (aΔ, qΔ) = partitionEithers [ (, _Δ') <$> unProp p | (p, _Δ') <- S.quotients _Δ ]

infix 4 |-
