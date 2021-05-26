module Focalized.Polarized
( Neg(..)
, Pos(..)
) where

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
