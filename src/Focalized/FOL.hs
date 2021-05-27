module Focalized.FOL
( FOL(..)
) where

import           Control.Applicative (Alternative(..))
import           Control.Effect.NonDet (foldMapA, guard)
import           Data.Either (partitionEithers)
import qualified Focalized.Multiset as S
import           Focalized.Proof

data FOL a
  = F a
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

instance Judgement FOL FOL where
  decomposeL p (_Γ :|-: _Δ) = case p of
    F _      -> empty
    Fls      -> pure ()
    Tru      -> empty -- no L rule for truth
    p :/\: q -> p <| q <| _Γ |- _Δ
    p :\/: q -> p <| _Γ |- _Δ >> q <| _Γ |- _Δ
    p :=>: q -> _Γ |- _Δ |> p >> q <| _Γ |- _Δ -- fixme: split _Γ & _Δ (multiplicative nondeterminism)
    Not p    -> _Γ |- _Δ |> p

  decomposeR (_Γ :|-: _Δ) = \case
    F _      -> empty
    Fls      -> empty -- no R rule for falsity
    Tru      -> pure ()
    p :/\: q -> _Γ |- _Δ |> p >> _Γ |- _Δ |> q -- fixme: split _Γ & _Δ (multiplicative nondeterminism)
    p :\/: q -> _Γ |- _Δ |> p <|> _Γ |- _Δ |> q
    p :=>: q -> p <| _Γ |- _Δ |> q
    Not p    -> p <| _Γ |- _Δ

unFOL = \case
  F a -> Left a
  p   -> Right p


(|-) :: (Alternative m, Monad m, Ord a) => Γ (FOL a) -> Δ (FOL a) -> m ()
_Γ |- _Δ = case (qΓ, qΔ) of
  ([], []) -> foldMapA (guard . (`elem` aΓ)) aΔ
  _        -> foldMapA (\ (p, _Γ') -> decomposeL p (_Γ' :|-: _Δ)) qΓ
          <|> foldMapA (\ (p, _Δ') -> decomposeR (_Γ :|-: _Δ') p) qΔ
  where
  (aΓ, qΓ) = partitionEithers [ (, _Γ') <$> unFOL p | (p, _Γ') <- S.quotients _Γ ]
  (aΔ, qΔ) = partitionEithers [ (, _Δ') <$> unFOL p | (p, _Δ') <- S.quotients _Δ ]

infix 4 |-
