module Focalized.Polarized
( N
, P
, Neg(..)
, Pos(..)
) where

data N
data P

data Neg n p a
  = N a
  | Bot
  | Top
  | n a :⅋: n a
  | n a :&: n a
  | p a :->: n a
  | Not (p a)
  | Up (p a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 :->:
infixr 7 :⅋:
infixr 8 :&:


data Pos n p a
  = P a
  | Zero
  | One
  | p a :+: p a
  | p a :*: p a
  | p a :-<: n a
  | Neg (n a)
  | Down (n a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 :-<:
infixr 7 :+:
infixr 8 :*:
