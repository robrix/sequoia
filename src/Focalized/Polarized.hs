{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoStarIsType #-}
module Focalized.Polarized
( Neg(..)
, Pos(..)
, ΓI(..)
, ΔI(..)
, L(..)
, R(..)
, Sequent(..)
) where

import           Control.Applicative (Alternative(..))
import           Control.Effect.NonDet (foldMapA, guard)
import           Control.Monad (ap)
import qualified Focalized.Multiset as S
import           Prelude hiding (head, tail)

data Neg a
  = NVar a
  | NBot
  | NTop
  | Neg a :⅋: Neg a
  | Neg a :&: Neg a
  | Pos a :->: Neg a
  | NNot (Neg a)
  | NUp (Pos a)
  deriving (Eq, Ord, Show, Foldable, Functor, Traversable)

infixr 6 :->:
infixr 7 :⅋:
infixr 8 :&:

instance Applicative Neg where
  pure = NVar
  (<*>) = ap

instance Monad Neg where
  m >>= f = case m of
    NVar a   -> f a
    NBot     -> NBot
    NTop     -> NTop
    a :⅋: b  -> (a >>= f) :⅋: (b >>= f)
    a :&: b  -> (a >>= f) :&: (b >>= f)
    a :->: b -> (a >>= PDown . f) :->: (b >>= f)
    NNot a   -> NNot (a >>= f)
    NUp a    -> NUp (a >>= PDown . f)


data Pos a
  = PVar a
  | PZero
  | POne
  | Pos a :+: Pos a
  | Pos a :*: Pos a
  | Pos a :--<: Neg a
  | PNeg (Pos a)
  | PDown (Neg a)
  deriving (Eq, Ord, Show, Foldable, Functor, Traversable)

infixr 6 :--<:
infixr 7 :+:
infixr 8 :*:

instance Applicative Pos where
  pure = PVar
  (<*>) = ap

instance Monad Pos where
  m >>= f = case m of
    PVar a    -> f a
    PZero     -> PZero
    POne      -> POne
    a :+: b   -> (a >>= f) :+: (b >>= f)
    a :*: b   -> (a >>= f) :*: (b >>= f)
    a :--<: b -> (a >>= f) :--<: (b >>= NUp . f)
    PNeg a    -> PNeg (a >>= f)
    PDown a   -> PDown (a >>= NUp . f)


data ΓI a = ΓI
  (S.Multiset (Pos a))
  (ΓS a)

class L a b c | a b -> c where
  (<|) :: a -> b -> c
  infixr 5 <|

instance Ord a => L a (ΓI a) (ΓI a) where
  a <| ΓI i s = ΓI i (S.insert (Left a) s)

instance Ord a => L (Neg a) (ΓI a) (ΓI a) where
  n <| ΓI i s = ΓI i (S.insert (Right n) s)

instance Ord a => L (Pos a) (ΓI a) (ΓI a) where
  p <| ΓI i s = ΓI (S.insert p i) s

instance L (Pos a) (ΓS a) (ΓI a) where
  p <| _Γ = ΓI (S.singleton p) _Γ

minInvertibleL :: Ord a => ΓI a -> Either (S.Multiset (Either a (Neg a))) (Pos a, ΓI a)
minInvertibleL (ΓI i s) = maybe (Left s) (\ (p, i') -> Right (p, ΓI i' s)) (S.minView i)

type ΓS a = S.Multiset (Either a (Neg a))


data ΔI a = ΔI
  (ΔS a)
  (S.Multiset (Neg a))

class R a b c | a b -> c where
  (|>) :: a -> b -> c
  infixl 5 |>

instance Ord a => R (ΔI a) a (ΔI a) where
  ΔI s i |> a = ΔI (S.insert (Right a) s) i

instance Ord a => R (ΔI a) (Neg a) (ΔI a) where
  ΔI s i |> n = ΔI s (S.insert n i)

instance Ord a => R (ΔI a) (Pos a) (ΔI a) where
  ΔI s i |> p = ΔI (S.insert (Left p) s) i

instance R (ΔS a) (Neg a) (ΔI a) where
  _Δ |> p = ΔI _Δ (S.singleton p)

minInvertibleR :: Ord a => ΔI a -> Either (S.Multiset (Either (Pos a) a)) (ΔI a, Neg a)
minInvertibleR (ΔI s i) = maybe (Left s) (\ (n, i') -> Right (ΔI s i', n)) (S.minView i)

type ΔS a = S.Multiset (Either (Pos a) a)


class Sequent l r where
  (|-) :: (Alternative m, Monad m) => l -> r -> m ()
  infix 4 |-

instance Ord a => Sequent (ΓS a) (ΔI a) where
  _Γ |- _Δ = ΓI mempty _Γ |- _Δ

instance Ord a => Sequent (ΓI a) (ΔS a) where
  _Γ |- _Δ = _Γ |- ΔI _Δ mempty

instance Ord a => Sequent (ΓI a) (ΔI a) where
  _Γ |- _Δ = case (minInvertibleL _Γ, minInvertibleR _Δ) of
    (Left  _Γ,      Left  _Δ)      -> _Γ |- _Δ
    (Right (p, _Γ), _)             -> case p of
      PVar a    -> a <| _Γ |- _Δ
      PZero     -> pure ()
      POne      -> _Γ |- _Δ
      p :+: q   -> p <| _Γ |- _Δ >> q <| _Γ |- _Δ
      p :*: q   -> p <| q <| _Γ |- _Δ
      p :--<: q -> p <| _Γ |- _Δ |> q
      PNeg p    -> _Γ |- _Δ |> p
      PDown p   -> p <| _Γ |- _Δ
    (_,             Right (_Δ, n)) -> case n of
      NVar a   -> _Γ |- _Δ |> a
      NBot     -> _Γ |- _Δ
      NTop     -> pure ()
      p :⅋: q  -> _Γ |- _Δ |> p |> q
      p :&: q  -> _Γ |- _Δ |> p >> _Γ |- _Δ |> q
      p :->: q -> p <| _Γ |- _Δ |> q
      NNot p   -> p <| _Γ |- _Δ
      NUp p    -> _Γ |- _Δ |> p

instance Ord a => Sequent (ΓS a) (ΔS a) where
  _Γ |- _Δ
    =   foldMapA (\ (p, _Γ') -> either (const empty) (\ n -> n :<: _Γ' |- _Δ) p) (S.quotients _Γ)
    <|> foldMapA (\ (p, _Δ') -> either (\ p -> _Γ |- _Δ' :>: p) (const empty) p) (S.quotients _Δ)

data a :<: b = a :<: b

infixr 5 :<:

data a :>: b = a :>: b

infixl 5 :>:

instance Ord a => Sequent (Neg a :<: ΓS a) (ΔS a) where
  n :<: _Γ |- _Δ = case n of
    NVar a   -> guard (Right a `elem` _Δ)
    NBot     -> pure ()
    NTop     -> empty -- no left rule for ⊤
    p :⅋: q  -> p :<: _Γ |- _Δ >> q :<: _Γ |- _Δ
    p :&: q  -> p :<: _Γ |- _Δ <|> q :<: _Γ |- _Δ
    p :->: q -> _Γ |- _Δ :>: p >> q :<: _Γ |- _Δ
    NNot p   -> _Γ |- _Δ |> p
    NUp p    -> p <| _Γ |- _Δ

instance Ord a => Sequent (ΓS a) (ΔS a :>: Pos a) where
  _Γ |- _Δ :>: p = case p of
    PVar a    -> guard (Left a `elem` _Γ)
    PZero     -> empty -- no right rule for 0
    POne      -> pure ()
    p :+: q   -> _Γ |- _Δ :>: p <|> _Γ |- _Δ :>: q
    p :*: q   -> _Γ |- _Δ :>: p >> _Γ |- _Δ :>: q
    p :--<: q -> _Γ |- _Δ :>: p >> q :<: _Γ |- _Δ
    PNeg p    -> p <| _Γ |- _Δ
    PDown p   -> _Γ |- _Δ |> p
