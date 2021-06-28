{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
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
  -- * Membership
, ContextL(..)
, ContextR(..)
) where

import Control.Monad (ap)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Focalized.Conjunction
import Focalized.Disjunction

-- Γ

data a < b = a :< b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 4 <, :<, <|

instance Conj (<) where
  inlr = (:<)
  exl (a :< _) = a
  exr (_ :< b) = b

instance Bifoldable (<) where
  bifoldMap = bifoldMapConj

instance Bifunctor (<) where
  bimap = bimapConj

instance Bitraversable (<) where
  bitraverse = bitraverseConj

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

-- | Discrimination of values in '>'.
--
-- @¬A ✕ ¬B -> ¬(A + B)@
(|>) :: (os -> r) -> (o -> r) -> ((os > o) -> r)
(|>) = (<-->)


-- Mixfix syntax

type l -| r = r l
type l |- r = l r

infixl 2 |-, -|


-- Membership

class ContextL a as as' | as a -> as', as as' -> a, as' a -> as where
  {-# MINIMAL ((selectL, dropL) | removeL), insertL #-}
  selectL :: as -> a
  selectL = exl . removeL
  dropL :: as -> as'
  dropL = exr . removeL
  removeL :: as -> (a, as')
  removeL = (,) <$> selectL <*> dropL
  insertL :: a -> as' -> as
  replaceL :: (ContextL b bs bs', bs' ~ as') => (a -> b) -> (as -> bs)
  replaceL f = uncurry (insertL . f) . removeL

instance {-# OVERLAPPING #-} ContextL a (a < as) as where
  selectL = exl
  dropL = exr
  removeL = inlr <$> exl <*> exr
  insertL = (<|)

instance {-# OVERLAPPING #-} ContextL a as as' => ContextL a (b < as) (b < as') where
  selectL = selectL . exr
  dropL (b :< as') = b <| dropL as'
  removeL (b :< as') = (b <|) <$> removeL as'
  insertL a (b :< as') = b <| insertL a as'


class ContextR a as as' | as a -> as', as as' -> a, as' a -> as where
  selectR :: as -> Maybe a
  selectR = exrD . removeR
  dropR :: as -> Maybe as'
  dropR = exlD . removeR
  removeR :: as -> Either as' a
  insertR :: Either as' a -> as
  replaceR :: (ContextR b bs bs', bs' ~ as') => (a -> b) -> (as -> bs)
  replaceR f = insertR . fmap f . removeR

instance {-# OVERLAPPING #-} ContextR a (as > a) as where
  selectR = exrD
  dropR = exlD
  removeR = inl <--> inr
  insertR = inl <--> inr

instance {-# OVERLAPPING #-} ContextR a as as' => ContextR a (as > b) (as' > b) where
  selectR = selectR <--> const Nothing
  dropR = fmap inl . dropR <--> Just . inr
  removeR = first inl . removeR <--> inl . inr
  insertR = first insertR . ((inl . inl <--> inr) <--> inl . inr)
