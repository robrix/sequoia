{-# LANGUAGE PolyKinds #-}
module Sequoia.Calculus.Context
( -- * Γ
  Γ(..)
, type (<)(..)
, (<|)
  -- * Δ
, Δ
, absurdΔ
, type (>)(..)
, (|>)
  -- * Mixfix syntax
, type (|-)
, type (-|)
) where

import Control.Monad (ap)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Sequoia.Conjunction
import Sequoia.Continuation
import Sequoia.Disjunction

-- Γ

data Γ = Γ

data a < b = a :< b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 4 <, :<, <|

instance Conj (<) where
  (-><-) = (:<)
  exl (a :< _) = a
  exr (_ :< b) = b

instance Bifoldable (<) where
  bifoldMap = bifoldMapConj

instance Bifunctor (<) where
  bimap = bimapConj

instance Bitraversable (<) where
  bitraverse = bitraverseConj

(<|) :: i -> is -> i < is
(<|) = (-><-)


-- Δ

data Δ

absurdΔ :: Δ -> a
absurdΔ = \case


data a > b
  = L a
  | R b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 4 >, |>

instance Disj (>) where
  inl = L
  inr = R
  f <--> g = \case
    L a -> f a
    R b -> g b

instance Bifoldable (>) where
  bifoldMap = bifoldMapDisj

instance Bifunctor (>) where
  bimap = bimapDisj

instance Bitraversable (>) where
  bitraverse = bitraverseDisj

instance Applicative ((>) a) where
  pure = R
  (<*>) = ap

instance Monad ((>) a) where
  (>>=) = flip (inl <-->)

-- | Discrimination of continuations in '>'.
--
-- @¬A ✕ ¬B -> ¬(A + B)@
(|>) :: Continuation k => k os b -> k o b -> k (os > o) b
(|>) = (<••>)


-- Mixfix syntax

type l -| r = r l
type l |- r = l r

infixl 2 |-, -|
