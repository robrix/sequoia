module Focalized.Polarized
( Neg(..)
, Pos(..)
) where

import Control.Applicative (Alternative(..))
import Control.Monad (ap)
import Focalized.Proof

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


data Pos a
  = P a
  | Zero
  | One
  | Pos a :+: Pos a
  | Pos a :*: Pos a
  | Pos a :-<: Neg a
  | Neg (Neg a)
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
    Neg a    -> Neg (a >>= Up . f)
    Down a   -> Down (a >>= Up . f)


instance Judgement Neg Pos where
  decomposeL p (_Γ :|-: _Δ) = case p of
    P _      -> empty
    Zero     -> pure ()
    One      -> _Γ |- _Δ
    p :+: q  -> p <| _Γ |- _Δ >> q <| _Γ |- _Δ
    p :*: q  -> p <| q <| _Γ |- _Δ
    p :-<: q -> p <| _Γ |- _Δ |> q
    Neg p    -> _Γ |- _Δ |> p
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

  unJudgementL = \case
    P a -> Left a
    p   -> Right p

  unJudgementR = \case
    N a -> Left a
    n   -> Right n
