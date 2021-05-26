module Focalized.FOL
( FOL(..)
, tru
, fls
, (==>)
, (\/)
, (/\)
, neg
, match
, (|-)
) where

import           Control.Applicative (Alternative(..))
import           Control.Effect.NonDet (foldMapA, guard)
import           Data.Either (partitionEithers)
import qualified Focalized.Multiset as S
import           Focalized.Proof


data FOL a
  = Fls
  | Tru
  | a :\/: a
  | a :/\: a
  | Not a
  | a :=>: a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 :=>:
infixr 7 :\/:
infixr 8 :/\:


tru, fls :: Prop FOL a

tru = P Tru
fls = P Fls

(==>), (\/), (/\) :: Prop FOL a -> Prop FOL a -> Prop FOL a

p ==> q = P (p :=>: q)
p \/ q = P (p :\/: q)
p /\ q = P (p :/\: q)

infixr 6 ==>
infixr 7 \/
infixr 8 /\

neg :: Prop FOL a -> Prop FOL a
neg p = P (Not p)


match :: (Alternative m, Monad m, Ord a) => Either ((Context FOL a, FOL (Prop FOL a)) :|-: Context FOL a) (Context FOL a :|-: (FOL (Prop FOL a), Context FOL a)) -> m ()
match = \case
  Left  ((_Γ, p) :|-: _Δ) -> case p of
    Fls      -> pure ()
    Tru      -> empty -- no L rule for truth
    p :/\: q -> p <| q <| _Γ |- _Δ
    p :\/: q -> p <| _Γ |- _Δ >> q <| _Γ |- _Δ
    p :=>: q -> _Γ |- _Δ |> p >> q <| _Γ |- _Δ -- fixme: split _Γ & _Δ (multiplicative nondeterminism)
    Not p    -> _Γ |- _Δ |> p
  Right (_Γ :|-: (p, _Δ)) -> case p of
    Fls      -> empty -- no R rule for falsity
    Tru      -> pure ()
    p :/\: q -> _Γ |- _Δ |> p >> _Γ |- _Δ |> q -- fixme: split _Γ & _Δ (multiplicative nondeterminism)
    p :\/: q -> (_Γ |- _Δ |> p) <|> (_Γ |- _Δ |> q)
    p :=>: q -> p <| _Γ |- _Δ |> q
    Not p    -> p <| _Γ |- _Δ

(|-) :: (Alternative m, Monad m, Ord a) => Context FOL a -> Context FOL a -> m ()
_Γ |- _Δ = case (qΓ, qΔ) of
  ([], []) -> foldMapA (guard . (`elem` aΓ)) aΔ
  _        -> foldMapA (\ (p, _Γ') -> match (Left  ((_Γ', p) :|-: _Δ))) qΓ
          <|> foldMapA (\ (p, _Δ') -> match (Right (_Γ :|-: (p, _Δ')))) qΔ
  where
  (aΓ, qΓ) = partitionEithers [ (, _Γ') <$> getProp p | (p, _Γ') <- S.quotients _Γ ]
  (aΔ, qΔ) = partitionEithers [ (, _Δ') <$> getProp p | (p, _Δ') <- S.quotients _Δ ]

infix 2 |-
