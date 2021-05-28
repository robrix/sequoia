module Focalized.Polarized
( Neg(..)
, Pos(..)
) where

import           Control.Applicative (Alternative(..))
import           Control.Effect.NonDet (foldMapA, guard)
import           Control.Monad (ap)
import           Data.Either (partitionEithers)
import qualified Focalized.Multiset as S
import           Focalized.Proof

data Neg a
  = N a
  | Bot
  | Top
  | Neg a :⅋: Neg a
  | Neg a :&: Neg a
  | Pos a :->: Neg a
  | Not (Pos a)
  | Up (Pos a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 :->:
infixr 7 :⅋:
infixr 8 :&:

instance Applicative Neg where
  pure = N
  (<*>) = ap

instance Monad Neg where
  m >>= f = case m of
    N a      -> f a
    Bot      -> Bot
    Top      -> Top
    a :⅋: b  -> (a >>= f) :⅋: (b >>= f)
    a :&: b  -> (a >>= f) :&: (b >>= f)
    a :->: b -> (a >>= Down . f) :->: (b >>= f)
    Not a    -> Not (a >>= Down . f)
    Up a     -> Up (a >>= Down . f)

unNeg = \case
  N a -> Left a
  n   -> Right n


data Pos a
  = P a
  | Zero
  | One
  | Pos a :+: Pos a
  | Pos a :*: Pos a
  | Pos a :-<: Neg a
  | Inv (Neg a)
  | Down (Neg a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 :-<:
infixr 7 :+:
infixr 8 :*:

instance Applicative Pos where
  pure = P
  (<*>) = ap

instance Monad Pos where
  m >>= f = case m of
    P a      -> f a
    Zero     -> Zero
    One      -> One
    a :+: b  -> (a >>= f) :+: (b >>= f)
    a :*: b  -> (a >>= f) :*: (b >>= f)
    a :-<: b -> (a >>= f) :-<: (b >>= Up . f)
    Inv a    -> Inv (a >>= Up . f)
    Down a   -> Down (a >>= Up . f)

unPos = \case
  P a -> Left a
  p   -> Right p


instance Judgement Neg Pos where
  decomposeL p (_Γ :|-: _Δ) = case p of
    P _      -> empty
    Zero     -> pure ()
    One      -> _Γ |- _Δ
    p :+: q  -> p <| _Γ |- _Δ >> q <| _Γ |- _Δ
    p :*: q  -> p <| q <| _Γ |- _Δ
    p :-<: q -> p <| _Γ |- _Δ |> q
    Inv p    -> _Γ |- _Δ |> p
    Down p   -> _Γ |- _Δ |> p

  decomposeR (_Γ :|-: _Δ) = \case
    N _      -> empty
    Bot      -> _Γ |- _Δ
    Top      -> pure ()
    p :⅋: q  -> _Γ |- _Δ |> p |> q
    p :&: q  -> _Γ |- _Δ |> p >> _Γ |- _Δ |> q
    p :->: q -> p <| _Γ |- _Δ |> q
    Not p    -> p <| _Γ |- _Δ
    Up p     -> p <| _Γ |- _Δ


class Sequent l r where
  (|-) :: (Alternative m, Monad m) => l -> r -> m ()
  infix 4 |-

instance Ord a => Sequent (Γ (Pos a)) (Δ (Neg a)) where
  _Γ |- _Δ = case (qΓ, qΔ) of
    ([], []) -> foldMapA (guard . (`elem` aΓ)) aΔ
    _        -> foldMapA (\ (p, _Γ') -> decomposeL p (_Γ' :|-: _Δ)) qΓ
            <|> foldMapA (\ (p, _Δ') -> decomposeR (_Γ :|-: _Δ') p) qΔ
    where
    (aΓ, qΓ) = partitionEithers [ (, _Γ') <$> unPos p | (p, _Γ') <- S.quotients _Γ ]
    (aΔ, qΔ) = partitionEithers [ (, _Δ') <$> unNeg p | (p, _Δ') <- S.quotients _Δ ]
