{-# LANGUAGE PolyKinds #-}
module Sequoia.Calculus.Context
( -- * Γ
  type (<)(..)
, (<|)
, unconsΓ
  -- * Δ
, type (>)(..)
, (|>)
, unsnocΔ
  -- * Mixfix syntax
, type (|-)
, type (-|)
) where

import Control.Applicative (liftA2)
import Control.Monad (ap)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Sequoia.Conjunction
import Sequoia.Continuation as K
import Sequoia.Disjunction
import Sequoia.Value as V

-- Γ

data a < b = a :< b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 4 <, :<, <|

instance Conj (<) where
  (>--<) = (:<)
  (>---<) = liftA2 (:<)
  exl (a :< _) = a
  exr (_ :< b) = b

instance Bifoldable (<) where
  bifoldMap = bifoldMapConj

instance Bifunctor (<) where
  bimap = bimapConj

instance Bitraversable (<) where
  bitraverse = bitraverseConj

-- | Prepend a value onto a '<'-context.
--
-- This is left- and right-inverse to 'unconsΓ':
--
-- @
-- 'uncurry' ('<|') . 'unconsΓ' = 'id'
-- @
-- @
-- 'unconsΓ' . 'uncurry' ('<|') = 'id'
-- @
(<|) :: V.Representable v => v i -> v is -> v (i < is)
(<|) = (>∘∘<)

-- | Split a '<'-context into its head and tail.
--
-- This is left- and right-inverse to '<|':
--
-- @
-- 'unconsΓ' . 'uncurry' ('<|') = 'id'
-- @
-- @
-- 'uncurry' ('<|') . 'unconsΓ' = 'id'
-- @
unconsΓ :: V.Representable v => v (a < b) -> (v a, v b)
unconsΓ v = (exlF v, exrF v)


-- Δ

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
--
-- This is left- and right-inverse to 'unsnocΔ':
--
-- @
-- 'uncurry' ('|>') . 'unsnocΔ' = id
-- @
-- @
-- 'unsnocΔ' . 'uncurry' ('|>') = id
-- @
(|>) :: K.Representable k => k os -> k o -> k (os > o)
(|>) = (<••>)

-- | Split a '>'-context into its initial and last parts.
--
-- This is left- and right-inverse to 'unsnocΔ':
--
-- @
-- 'uncurry' ('|>') . 'unsnocΔ' = id
-- @
-- @
-- 'unsnocΔ' . 'uncurry' ('|>') = id
-- @
unsnocΔ :: K.Representable k => k (a > b) -> (k a, k b)
unsnocΔ k = (inlK k, inrK k)


-- Mixfix syntax

type l -| r = r l
type l |- r = l r

infixl 2 |-, -|
