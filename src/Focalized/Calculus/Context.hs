{-# LANGUAGE PolyKinds #-}
module Focalized.Calculus.Context
( -- * Γ
  type (<)(..)
, (<|)
  -- * Δ
, type (>)(..)
, (|>)
  -- * Mixfix syntax
, type (|-)
, type (-|)
) where

import Control.Monad (ap)
import Focalized.Connective

-- Γ

data a < b = a :< b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 4 <, :<, <|

instance Conj (<) where
  inlr = (:<)
  exl (a :< _) = a
  exr (_ :< b) = b

(<|) :: i -> is -> i < is
(<|) = inlr


-- Δ

data a > b
  = L a
  | R b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 4 >, |>

instance Disj (>) where
  inl = L
  inr = R
  exlr f g = \case
    L a -> f a
    R b -> g b

instance Applicative ((>) a) where
  pure = R
  (<*>) = ap

instance Monad ((>) a) where
  (>>=) = flip (exlr inl)

-- | Discrimination of values in '>'.
--
-- @¬A ✕ ¬B -> ¬(A + B)@
(|>) :: (os -> r) -> (o -> r) -> ((os > o) -> r)
(|>) = exlr


-- Mixfix syntax

type l -| r = r l
type l |- r = l r

infixl 2 |-, -|
