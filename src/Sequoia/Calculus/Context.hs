{-# LANGUAGE PolyKinds #-}
module Sequoia.Calculus.Context
( -- * Γ
  Γ(..)
, type (<)(..)
, (<|)
, (<↑)
  -- * Δ
, Δ
, absurdΔ
, type (>)(..)
, (|>)
, (↓>)
  -- * Mixfix syntax
, type (|-)
, type (-|)
) where

import Control.Monad (ap)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Sequoia.CPS
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

(<↑) :: (Contravariant k, Conj c) => k (a `c` _Γ) -> a -> k _Γ
k <↑ a = k •<< (a -><-)

infixl 7 <↑


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
(|>) :: Continuation k => k os -> k o -> k (os > o)
(|>) = (<••>)

(↓>) :: (ContPassing k c, Disj d) => k a -> c _Γ (_Δ `d` a) -> c _Γ _Δ
a ↓> c = inC (exC c . (<••> a))

infixr 9 ↓>


-- Mixfix syntax

type l -| r = r l
type l |- r = l r

infixl 2 |-, -|
