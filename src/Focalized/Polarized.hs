module Focalized.Polarized
( Neg(..)
, Pos(..)
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

data Neg a
  = N a
  | Bot
  | Top
  | Neg a :⅋: Neg a
  | Neg a :&: Neg a
  | Pos a :->: Neg a
  | Not (Neg a)
  | Up (Pos a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 :->:
infixr 7 :⅋:
infixr 8 :&:

instance Applicative Neg where
  pure = N
  (<*>) = ap

instance Monad Neg where
  m >>= f = case m of
    N a      -> f a
    Bot      -> Bot
    Top      -> Top
    a :⅋: b  -> (a >>= f) :⅋: (b >>= f)
    a :&: b  -> (a >>= f) :&: (b >>= f)
    a :->: b -> (a >>= Down . f) :->: (b >>= f)
    Not a    -> Not (a >>= f)
    Up a     -> Up (a >>= Down . f)

unNeg = \case
  N a -> Left a
  n   -> Right n


data Pos a
  = P a
  | Zero
  | One
  | Pos a :+: Pos a
  | Pos a :*: Pos a
  | Pos a :-<: Neg a
  | Inv (Pos a)
  | Down (Neg a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 :-<:
infixr 7 :+:
infixr 8 :*:

instance Applicative Pos where
  pure = P
  (<*>) = ap

instance Monad Pos where
  m >>= f = case m of
    P a      -> f a
    Zero     -> Zero
    One      -> One
    a :+: b  -> (a >>= f) :+: (b >>= f)
    a :*: b  -> (a >>= f) :*: (b >>= f)
    a :-<: b -> (a >>= f) :-<: (b >>= Up . f)
    Inv a    -> Inv (a >>= f)
    Down a   -> Down (a >>= Up . f)

unPos = \case
  P a -> Left a
  p   -> Right p


instance Judgement Neg Pos where
  decomposeL p (_Γ :|-: _Δ) = case p of
    P _      -> empty
    Zero     -> pure ()
    One      -> _Γ |- _Δ
    p :+: q  -> p <| _Γ |- _Δ >> q <| _Γ |- _Δ
    p :*: q  -> p <| q <| _Γ |- _Δ
    p :-<: q -> p <| _Γ |- _Δ |> q
    Inv p    -> _Γ |- _Δ |> Up p
    Down p   -> _Γ |- _Δ |> p

  decomposeR (_Γ :|-: _Δ) = \case
    N _      -> empty
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

instance Ord a => Sequent (Γ (Pos a)) (Δ (Neg a)) where
  _Γ |- _Δ = case (qΓ, qΔ) of
    ([], []) -> foldMapA (guard . (`elem` aΓ)) aΔ
    _        -> foldMapA (\ (p, _Γ') -> decomposeL p (_Γ' :|-: _Δ)) qΓ
            <|> foldMapA (\ (p, _Δ') -> decomposeR (_Γ :|-: _Δ') p) qΔ
    where
    (aΓ, qΓ) = partitionEithers [ (, _Γ') <$> unPos p | (p, _Γ') <- S.quotients _Γ ]
    (aΔ, qΔ) = partitionEithers [ (, _Δ') <$> unNeg p | (p, _Δ') <- S.quotients _Δ ]


inversion :: (Alternative m, Monad m, Ord a) => (Γ (Pos a), Γ (Either a (Neg a))) :|-: (Δ (Either (Pos a) a), Δ (Neg a)) -> m ()
inversion ((iΓ, _Γ) :|-: (_Δ, iΔ)) = case (S.minView iΓ, S.minView iΔ) of
  (Nothing,      Nothing)       -> neutral (_Γ :|-: _Δ)
  (Just (p, iΓ), _)             -> case p of
    P a      -> inversion ((iΓ, Left a <| _Γ) :|-: (_Δ, iΔ))
    Zero     -> pure ()
    One      -> inversion ((iΓ, _Γ) :|-: (_Δ, iΔ))
    p :+: q  -> inversion ((p <| iΓ, _Γ) :|-: (_Δ, iΔ)) >> inversion ((q <| iΓ, _Γ) :|-: (_Δ, iΔ))
    p :*: q  -> inversion ((p <| q <| iΓ, _Γ) :|-: (_Δ, iΔ))
    p :-<: q -> inversion ((p <| iΓ, _Γ) :|-: (_Δ, iΔ |> q))
    Inv p    -> inversion ((iΓ, _Γ) :|-: (_Δ |> Left p, iΔ))
    Down p   -> inversion ((iΓ, Right p <| _Γ) :|-: (_Δ, iΔ))
  (_,            Just (n, iΔ)) -> case n of
    N a      -> inversion ((iΓ, _Γ) :|-: (_Δ |> Right a, iΔ))
    Bot      -> inversion ((iΓ, _Γ) :|-: (_Δ, iΔ))
    Top      -> pure ()
    p :⅋: q  -> inversion ((iΓ, _Γ) :|-: (_Δ, iΔ |> p |> q))
    p :&: q  -> inversion ((iΓ, _Γ) :|-: (_Δ, iΔ |> p)) >> inversion ((iΓ, _Γ) :|-: (_Δ, iΔ |> q))
    p :->: q -> inversion ((p <| iΓ, _Γ) :|-: (_Δ, iΔ |> q))
    Not p    -> inversion ((iΓ, Right p <| _Γ) :|-: (_Δ, iΔ))
    Up p     -> inversion ((iΓ, _Γ) :|-: (_Δ |> Left p, iΔ))

neutral :: (Alternative m, Monad m, Ord a) => Γ (Either a (Neg a)) :|-: Δ (Either (Pos a) a) -> m ()
neutral (_Γ :|-: _Δ)
  =   foldMapA (\ (p, _Γ') -> either (const empty) (\ n -> focusL ((n, _Γ') :|-: _Δ)) p) (S.quotients _Γ)
  <|> foldMapA (\ (p, _Δ') -> either (\ p -> focusR (_Γ :|-: (_Δ', p))) (const empty) p) (S.quotients _Δ)

focusL :: (Alternative m, Monad m, Ord a) => (Neg a, Γ (Either a (Neg a))) :|-: Δ (Either (Pos a) a) -> m ()
focusL ((n, _Γ) :|-: _Δ) = case n of
  N a      -> guard (Right a `elem` _Δ)
  Bot      -> pure ()
  Top      -> empty -- no left rule for ⊤
  p :⅋: q  -> focusL ((p, _Γ) :|-: _Δ) <|> focusL ((q, _Γ) :|-: _Δ)
  p :&: q  -> focusL ((p, _Γ) :|-: _Δ) >> focusL ((q, _Γ) :|-: _Δ)
  p :->: q -> focusR (_Γ :|-: (_Δ, p)) >> focusL ((q, _Γ) :|-: _Δ)
  Not p    -> inversion ((mempty, _Γ) :|-: (_Δ, S.singleton p))
  Up p     -> inversion ((S.singleton p, _Γ) :|-: (_Δ, mempty))

focusR :: (Alternative m, Monad m, Ord a) => Γ (Either a (Neg a)) :|-: (Δ (Either (Pos a) a), Pos a) -> m ()
focusR (_Γ :|-: (_Δ, p)) = case p of
  P a      -> guard (Left a `elem` _Γ)
  Zero     -> empty -- no right rule for 0
  One      -> pure ()
  p :+: q  -> focusR (_Γ :|-: (_Δ, p)) <|> focusR (_Γ :|-: (_Δ, q))
  p :*: q  -> focusR (_Γ :|-: (_Δ, p)) >> focusR (_Γ :|-: (_Δ, q))
  p :-<: q -> focusR (_Γ :|-: (_Δ, p)) >> focusL ((q, _Γ) :|-: _Δ)
  Inv p    -> inversion ((S.singleton p, _Γ) :|-: (_Δ, mempty))
  Down p   -> inversion ((mempty, _Γ) :|-: (_Δ, S.singleton p))
