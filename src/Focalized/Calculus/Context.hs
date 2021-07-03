{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
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
  -- * Mixfix syntax
, type (|-)
, type (-|)
  -- * Membership
, mkV
, type (:.)(..)
, MemberΓ(..)
, replaceΓ
, MemberΔ(..)
, replaceΔ
, ElemL(..)
, replaceL
, ElemR(..)
, replaceR
) where

import Control.Applicative (liftA2)
import Control.Monad (ap)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Coerce (coerce)
import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Functor.Rep
import Focalized.Conjunction
import Focalized.Continuation
import Focalized.Disjunction

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
-- @¬A ✕ ¬B -> ¬(A + V)@
(|>) :: r •os -> r •o -> r •(os > o)
(|>) = (<••>)


-- Mixfix syntax

type l -| r = r l
type l |- r = l r

infixl 2 |-, -|


-- Membership

-- | Convenience to construct a named variable given the same name available for use inside. This can obviate the need for @-XScopedTypeVariables@ in some situations which would otherwise require them.
mkV :: (n :. () -> a) -> n :. a
mkV f = V (f (V ()))

newtype (n :: k) :. a = V { getV :: a }
  deriving (Functor)
  deriving (Applicative, Monad, Representable) via Identity

infixr 5 :.

instance Distributive ((:.) n) where
  distribute = V . fmap getV

instance Adjunction ((:.) n) ((:.) n) where
  unit   = coerce
  counit = coerce

  leftAdjunct  = coerce
  rightAdjunct = coerce


class ConcatΓ as bs cs | as bs -> cs, as cs -> bs, bs cs -> as where
  concatΓ :: as -> bs -> cs

instance ConcatΓ as Γ as where
  concatΓ = const

instance ConcatΓ as bs cs => ConcatΓ (a < as) bs (a < cs) where
  concatΓ (a :< as) bs = a :< concatΓ as bs


class ConcatΔ as bs cs | as bs -> cs, as cs -> bs, bs cs -> as where
  concatΔ :: r •as -> r •bs -> r •cs

instance ConcatΔ as Δ as where
  concatΔ = const

instance ConcatΔ as bs cs => ConcatΔ (as > a) bs (cs > a) where
  concatΔ as bs = concatΔ (inlC as) bs |> inrC as


class MemberΓ n a as as' | n a as -> as', as as' -> n a where
  injectΓ :: n :. (a, as') -> n :. as
  rejectΓ :: n :. as -> n :. (a, as')

instance MemberΓ n a (n :. a < as) as where
  injectΓ = liftA2 (<|) <$> fmap    V . exlF <*> exrF
  rejectΓ = liftA2 (,)  <$> fmap getV . exlF <*> exrF

instance MemberΓ n a as as' => MemberΓ n a (n' :. b < as) (n' :. b < as') where
  injectΓ = liftA2 (<|) <$> exlF . exrF <*> injectΓ . fmap exrF
  rejectΓ = rightAdjunct (\ (b :< as) -> leftAdjunct (fmap (fmap (b <|)) . rejectΓ) as)

replaceΓ :: (MemberΓ n a as as', MemberΓ n b bs as') => (a -> b) -> (n :. as -> n :. bs)
replaceΓ f = injectΓ . fmap (first f) . rejectΓ


class MemberΔ n a as as' | n a as -> as', as as' -> n a where
  injectΔ :: n :. (r •as', r •a) -> n :. r •as
  rejectΔ :: n :. r •as -> n :. (r •as', r •a)

instance MemberΔ n a (as > n :. a) as where
  injectΔ = liftA2 (|>) <$>      exlF <*> fmap (contramap getV . exr)
  rejectΔ = liftA2 (,)  <$> fmap inlC <*> fmap (contramap (inr . V))

instance MemberΔ n a as as' => MemberΔ n a (as > n' :. b) (as' > n' :. b) where
  injectΔ = liftA2 (|>) <$> injectΔ . fmap (first inlC) <*> fmap inrC . exlF
  rejectΔ = rightAdjunct (\ as -> leftAdjunct (fmap (first (|> inrC as)) . rejectΔ) (inlC as))

replaceΔ :: (MemberΔ n a as as', MemberΔ n b bs as') => (b -> a) -> (n :. r •as -> n :. r •bs)
replaceΔ f = injectΔ . fmap (fmap (contramap f)) . rejectΔ


class ElemL a as as' | a as -> as', as as' -> a where
  injectL :: (a, as') -> as
  rejectL :: as -> (a, as')

instance ElemL a (a < as) as where
  injectL = (<|) <$> exl <*> exr
  rejectL = (,)  <$> exl <*> exr

instance ElemL a as as' => ElemL a (b < as) (b < as') where
  injectL =        (<|) <$> exl . exr <*> injectL . exrF
  rejectL = fmap . (<|) <$> exl       <*> rejectL . exr

replaceL :: (ElemL a as as', ElemL b bs as') => (a -> b) -> (as -> bs)
replaceL f = injectL . first f . rejectL


class ElemR a as as' | a as -> as', as as' -> a where
  injectR :: (r •as', r •a) -> r •as
  rejectR :: r •as -> (r •as', r •a)

instance ElemR a (as > a) as where
  injectR = (|>) <$> exl  <*> exr
  rejectR = (,)  <$> inlC <*> inrC

instance ElemR a as as' => ElemR a (as > b) (as' > b) where
  injectR =              (|>) <$> injectR . first inlC <*>           inrC . exl
  rejectR = first . flip (|>) <$>                 inrC <*> rejectR . inlC

replaceR :: (ElemR a as as', ElemR b bs as') => (b -> a) -> (r •as -> r •bs)
replaceR f = injectR . fmap (contramap f) . rejectR
