module Focalized.Polarized
( N
, P
, Neg(..)
, Pos(..)
) where

data N
data P

data Neg a
  = Bot
  | Top
  | a :⅋: a
  | a :&: a
  | a :->: a
  | Not a
  | Up a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 :->:
infixr 7 :⅋:
infixr 8 :&:


data Pos a
  = Zero
  | One
  | a :+: a
  | a :*: a
  | a :-<: a
  | Neg a
  | Down a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 :-<:
infixr 7 :+:
infixr 8 :*:
