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
import           Data.Either (partitionEithers)
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
  m >>= f = case m of
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

unProp :: Prop polarity a -> Either a (Prop polarity a)
unProp = \case
  V a -> Left a
  p   -> Right p


instance Judgement (Prop N) (Prop P) where
  decomposeL p (_Γ :|-: _Δ) = case p of
    V _      -> empty
    Zero     -> pure ()
    One      -> _Γ |- _Δ
    p :+: q  -> p <| _Γ |- _Δ >> q <| _Γ |- _Δ
    p :*: q  -> p <| q <| _Γ |- _Δ
    p :-<: q -> p <| _Γ |- _Δ |> q
    Inv p    -> _Γ |- _Δ |> Up p
    Down p   -> _Γ |- _Δ |> p

  decomposeR (_Γ :|-: _Δ) = \case
    V _      -> empty
    Bot      -> _Γ |- _Δ
    Top      -> pure ()
    p :⅋: q  -> _Γ |- _Δ |> p |> q
    p :&: q  -> _Γ |- _Δ |> p >> _Γ |- _Δ |> q
    p :->: q -> p <| _Γ |- _Δ |> q
    Not p    -> Down p <| _Γ |- _Δ
    Up p     -> p <| _Γ |- _Δ


class Sequent l r where
  (|-) :: (Alternative m, Monad m) => l -> r -> m ()
  infix 4 |-

instance Ord a => Sequent (Γ (Prop P a)) (Δ (Prop N a)) where
  _Γ |- _Δ = case (qΓ, qΔ) of
    ([], []) -> foldMapA (guard . (`elem` aΓ)) aΔ
    _        -> foldMapA (\ (p, _Γ') -> decomposeL p (_Γ' :|-: _Δ)) qΓ
            <|> foldMapA (\ (p, _Δ') -> decomposeR (_Γ :|-: _Δ') p) qΔ
    where
    (aΓ, qΓ) = partitionEithers [ (, _Γ') <$> unProp p | (p, _Γ') <- S.quotients _Γ ]
    (aΔ, qΔ) = partitionEithers [ (, _Δ') <$> unProp p | (p, _Δ') <- S.quotients _Δ ]


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
