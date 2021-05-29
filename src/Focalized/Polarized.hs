{-# LANGUAGE GADTs #-}
module Focalized.Polarized
( N
, P
, Prop(..)
, inversion
, neutral
, focusL
, focusR
) where

import           Control.Applicative (Alternative(..))
import           Control.Effect.NonDet (foldMapA, guard)
import           Control.Monad (ap)
import qualified Focalized.Multiset as S
import           Focalized.Proof

data N
data P

data Prop polarity a where
  V :: a -> Prop polarity a
  Bot :: Prop N a
  Top :: Prop N a
  (:⅋:) :: Prop N a -> Prop N a -> Prop N a
  (:&:) :: Prop N a -> Prop N a -> Prop N a
  (:->:) :: Prop P a -> Prop N a -> Prop N a
  Not :: Prop N a -> Prop N a
  Up :: Prop P a -> Prop N a
  Zero :: Prop P a
  One :: Prop P a
  (:+:) :: Prop P a -> Prop P a -> Prop P a
  (:*:) :: Prop P a -> Prop P a -> Prop P a
  (:-<:) :: Prop P a -> Prop N a -> Prop P a
  Inv :: Prop P a -> Prop P a
  Down :: Prop N a -> Prop P a

deriving instance Eq a => Eq (Prop polaritty a)
deriving instance Ord a => Ord (Prop polaritty a)
deriving instance Show a => Show (Prop polaritty a)
deriving instance Foldable (Prop polaritty)
deriving instance Functor (Prop polaritty)
deriving instance Traversable (Prop polaritty)

infixr 6 :->:
infixr 7 :⅋:
infixr 8 :&:

infixr 6 :-<:
infixr 7 :+:
infixr 8 :*:

instance Applicative (Prop polarity) where
  pure = V
  (<*>) = ap

instance Monad (Prop polarity) where
  (>>=) = bind

bind :: Prop polarity a -> (a -> Prop polarity b) -> Prop polarity b
bind m f = case m of
  V a      -> f a
  Bot      -> Bot
  Top      -> Top
  a :⅋: b  -> (a >>= f) :⅋: (b >>= f)
  a :&: b  -> (a >>= f) :&: (b >>= f)
  a :->: b -> (a >>= Down . f) :->: (b >>= f)
  Not a    -> Not (a >>= f)
  Up a     -> Up (a >>= Down . f)
  Zero     -> Zero
  One      -> One
  a :+: b  -> (a >>= f) :+: (b >>= f)
  a :*: b  -> (a >>= f) :*: (b >>= f)
  a :-<: b -> (a >>= f) :-<: (b >>= Up . f)
  Inv a    -> Inv (a >>= f)
  Down a   -> Down (a >>= Up . f)


inversion :: (Alternative m, Monad m, Ord a) => (Γ (Prop P a), Γ (Either a (Prop N a))) :|-: (Δ (Either (Prop P a) a), Δ (Prop N a)) -> m ()
inversion ((iΓ, _Γ) :|-: (_Δ, iΔ)) = case (S.minView iΓ, S.minView iΔ) of
  (Nothing,      Nothing)       -> neutral (_Γ :|-: _Δ)
  (Just (p, iΓ), _)             -> case p of
    V a      -> inversion ((iΓ, Left a <| _Γ) :|-: (_Δ, iΔ))
    Zero     -> pure ()
    One      -> inversion ((iΓ, _Γ) :|-: (_Δ, iΔ))
    p :+: q  -> inversion ((p <| iΓ, _Γ) :|-: (_Δ, iΔ)) >> inversion ((q <| iΓ, _Γ) :|-: (_Δ, iΔ))
    p :*: q  -> inversion ((p <| q <| iΓ, _Γ) :|-: (_Δ, iΔ))
    p :-<: q -> inversion ((p <| iΓ, _Γ) :|-: (_Δ, iΔ |> q))
    Inv p    -> inversion ((iΓ, _Γ) :|-: (_Δ |> Left p, iΔ))
    Down p   -> inversion ((iΓ, Right p <| _Γ) :|-: (_Δ, iΔ))
  (_,            Just (n, iΔ)) -> case n of
    V a      -> inversion ((iΓ, _Γ) :|-: (_Δ |> Right a, iΔ))
    Bot      -> inversion ((iΓ, _Γ) :|-: (_Δ, iΔ))
    Top      -> pure ()
    p :⅋: q  -> inversion ((iΓ, _Γ) :|-: (_Δ, iΔ |> p |> q))
    p :&: q  -> inversion ((iΓ, _Γ) :|-: (_Δ, iΔ |> p)) >> inversion ((iΓ, _Γ) :|-: (_Δ, iΔ |> q))
    p :->: q -> inversion ((p <| iΓ, _Γ) :|-: (_Δ, iΔ |> q))
    Not p    -> inversion ((iΓ, Right p <| _Γ) :|-: (_Δ, iΔ))
    Up p     -> inversion ((iΓ, _Γ) :|-: (_Δ |> Left p, iΔ))

neutral :: (Alternative m, Monad m, Ord a) => Γ (Either a (Prop N a)) :|-: Δ (Either (Prop P a) a) -> m ()
neutral (_Γ :|-: _Δ)
  =   foldMapA (\ (p, _Γ') -> either (const empty) (\ n -> focusL ((n, _Γ') :|-: _Δ)) p) (S.quotients _Γ)
  <|> foldMapA (\ (p, _Δ') -> either (\ p -> focusR (_Γ :|-: (_Δ', p))) (const empty) p) (S.quotients _Δ)

focusL :: (Alternative m, Monad m, Ord a) => (Prop N a, Γ (Either a (Prop N a))) :|-: Δ (Either (Prop P a) a) -> m ()
focusL ((n, _Γ) :|-: _Δ) = case n of
  V a      -> guard (Right a `elem` _Δ)
  Bot      -> pure ()
  Top      -> empty -- no left rule for ⊤
  p :⅋: q  -> focusL ((p, _Γ) :|-: _Δ) <|> focusL ((q, _Γ) :|-: _Δ)
  p :&: q  -> focusL ((p, _Γ) :|-: _Δ) >> focusL ((q, _Γ) :|-: _Δ)
  p :->: q -> focusR (_Γ :|-: (_Δ, p)) >> focusL ((q, _Γ) :|-: _Δ)
  Not p    -> inversion ((mempty, _Γ) :|-: (_Δ, S.singleton p))
  Up p     -> inversion ((S.singleton p, _Γ) :|-: (_Δ, mempty))

focusR :: (Alternative m, Monad m, Ord a) => Γ (Either a (Prop N a)) :|-: (Δ (Either (Prop P a) a), Prop P a) -> m ()
focusR (_Γ :|-: (_Δ, p)) = case p of
  V a      -> guard (Left a `elem` _Γ)
  Zero     -> empty -- no right rule for 0
  One      -> pure ()
  p :+: q  -> focusR (_Γ :|-: (_Δ, p)) <|> focusR (_Γ :|-: (_Δ, q))
  p :*: q  -> focusR (_Γ :|-: (_Δ, p)) >> focusR (_Γ :|-: (_Δ, q))
  p :-<: q -> focusR (_Γ :|-: (_Δ, p)) >> focusL ((q, _Γ) :|-: _Δ)
  Inv p    -> inversion ((S.singleton p, _Γ) :|-: (_Δ, mempty))
  Down p   -> inversion ((mempty, _Γ) :|-: (_Δ, S.singleton p))
