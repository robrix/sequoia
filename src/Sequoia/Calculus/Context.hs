{-# LANGUAGE PolyKinds #-}
module Sequoia.Calculus.Context
( -- * Γ
  type (<)(..)
, (<|)
, unconsΓ
, consΓ
, lΓ
, rΓ
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
import Fresnel.Iso
import Fresnel.Lens
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value as V

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
(<|) :: e ∘ i -> e ∘ is -> e ∘ (i < is)
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
unconsΓ :: e ∘ (a < b) -> (e ∘ a, e ∘ b)
unconsΓ v = (exlF v, exrF v)

consΓ :: Iso
  (e ∘ (i    < is)) (e' ∘ (i'     < is'))
  (e ∘  i, e ∘ is)  (e' ∘  i', e' ∘ is')
consΓ = iso unconsΓ (uncurry (<|))


lΓ :: Lens
  (e ∘ (i < is)) (e ∘ (i' < is))
  (e ∘  i)       (e ∘  i')
lΓ = lens exlF (\ iis i' -> first . const <$> i' <*> iis)

rΓ :: Lens
  (e ∘ (i < is)) (e ∘ (i < is'))
  (e ∘      is)  (e ∘      is')
rΓ = lens exrF (\ iis is' -> second . const <$> is' <*> iis)


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
(|>) :: os • r -> o • r -> (os > o) • r
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
unsnocΔ :: (a > b) • r -> (a • r, b • r)
unsnocΔ k = (inlK k, inrK k)


-- Mixfix syntax

type l -| r = r l
type l |- r = l r

infixl 2 |-, -|
