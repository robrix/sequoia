{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus.Context
( -- * Γ
  Γ(..)
, type (<)(..)
, (<|)
  -- * Δ
, Δ
, absurdΔ
, type (>)(..)
, (|>)
, (||>)
  -- * Mixfix syntax
, type (|-)
, type (-|)
  -- * Membership
, type (?)(..)
, type (:::)(..)
, ContextL(..)
, ContextR(..)
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Identity
import Data.Functor.Rep
import Focalized.CPS
import Focalized.Conjunction
import Focalized.Disjunction
import GHC.Base

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

-- | Discrimination of values in '>'.
--
-- @¬A ✕ ¬B -> ¬(A + B)@
(|>) :: (os -> r) -> (o -> r) -> ((os > o) -> r)
(|>) = (<-->)

-- | Discrimination of continuations in '>'.
--
-- @¬A ✕ ¬B -> ¬(A + B)@
(||>) :: r •os -> r •o -> r •(os > o)
(||>) = liftK2 (<-->)


-- Mixfix syntax

type l -| r = r l
type l |- r = l r

infixl 2 |-, -|


-- Membership

newtype (n :: Symbol) ? a = Q { getQ :: a }
  deriving (Functor)
  deriving (Applicative, Monad, Representable) via Identity

infixr 8 ?

instance Distributive ((?) n) where
  distribute = Q . fmap getQ

instance Adjunction ((?) n) ((?) n) where
  unit   = coerce
  counit = coerce

  leftAdjunct  = coerce
  rightAdjunct = coerce


newtype (n :: Symbol) ::: a = B { getB :: a }
  deriving (Functor)
  deriving (Applicative, Monad, Representable) via Identity

infix 3 :::

instance Distributive ((:::) n) where
  distribute = B . fmap getB

instance Adjunction ((:::) n) ((:::) n) where
  unit   = coerce
  counit = coerce

  leftAdjunct  = coerce
  rightAdjunct = coerce


class ContextL (n :: Symbol) a as as' | as a -> as', as as' -> a, as n -> a, as' n a -> as where
  {-# MINIMAL ((selectL, dropL) | removeL), insertL #-}
  selectL :: n ? as -> n ? a
  selectL = fmap exl . removeL
  dropL :: n ? as -> n ? as'
  dropL = fmap exr . removeL
  removeL :: n ? as -> n ? (a, as')
  removeL = liftA2 (,) <$> selectL <*> dropL
  insertL :: n ? (a, as') -> n ? as
  replaceL :: (ContextL n' b bs bs', n ~ n', bs' ~ as') => (a -> b) -> (n ? as -> n ? bs)
  replaceL f = insertL . fmap (first f) . removeL

instance {-# OVERLAPPING #-} ContextL n a ((n ::: a) < as) as where
  selectL = fmap (getB . exl)
  dropL = fmap exr
  removeL = liftA2 (-><-) <$> fmap (getB . exl) <*> fmap exr
  insertL = fmap (uncurry ((<|) . B))

instance {-# OVERLAPPING #-} ContextL n a as as' => ContextL n a (b < as) (b < as') where
  selectL = selectL . fmap exr
  dropL = fmap . (<|) <$> exl . getQ <*> dropL . fmap exr
  removeL = fmap . fmap . (<|) <$> exl . getQ <*> removeL . fmap exr
  insertL = fmap . (<|) <$> exl . exr . getQ <*> insertL . fmap (fmap exr)


class ContextR (n :: Symbol) a as as' | as a -> as', as as' -> a, as n -> a, as' n a -> as where
  selectR :: n ? as -> n ? Maybe a
  selectR = fmap exrD . removeR
  dropR :: n ? as -> n ? Maybe as'
  dropR = fmap exlD . removeR
  removeR :: n ? as -> n ? Either as' a
  insertR :: n ? Either as' a -> n ? as
  replaceR :: (ContextR n b bs bs', bs' ~ as') => (a -> b) -> (n ? as -> n ? bs)
  replaceR f = insertR . fmap (fmap f) . removeR

instance {-# OVERLAPPING #-} ContextR n a (as > (n ::: a)) as where
  selectR = fmap (fmap getB . exrD)
  dropR = fmap exlD
  removeR = fmap (inl <--> inr . getB)
  insertR = fmap (fmap B . (inl <--> inr))

instance {-# OVERLAPPING #-} ContextR n a as as' => ContextR n a (as > b) (as' > b) where
  selectR = selectR -||- const (pure Nothing)
  dropR = fmap (fmap inl) . dropR -||- fmap (Just . inr)
  removeR = fmap (first inl) . removeR -||- fmap (inl . inr)
  insertR = (fmap inl . insertR . fmap inl -||- fmap inr) -||- fmap inl . insertR . fmap inr
