module Focalized.Polarized
( Neg(..)
, Pos(..)
, ΓI(..)
, ΔI(..)
, L(..)
, R(..)
) where

import           Control.Applicative (Alternative(..))
import           Control.Effect.NonDet (foldMapA, guard)
import           Control.Monad (ap)
import qualified Focalized.Multiset as S

data Neg a
  = N a
  | Bot
  | Top
  | Neg a :⅋: Neg a
  | Neg a :&: Neg a
  | Pos a :->: Neg a
  | Not (Neg a)
  | Up (Pos a)
  deriving (Eq, Ord, Show, Foldable, Functor, Traversable)

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


data Pos a
  = P a
  | Zero
  | One
  | Pos a :+: Pos a
  | Pos a :*: Pos a
  | Pos a :-<: Neg a
  | Inv (Pos a)
  | Down (Neg a)
  deriving (Eq, Ord, Show, Foldable, Functor, Traversable)

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


type Γ = S.Multiset
type Δ = S.Multiset

data ΓI a = ΓI
  (S.Multiset (Pos a))
  (ΓS a)

class Ord a => L a p where
  (<|) :: p -> ΓI a -> ΓI a
  infixr 5 <|

instance Ord a => L a a where
  a <| ΓI i s = ΓI i (S.insert (Left a) s)

instance Ord a => L a (Neg a) where
  n <| ΓI i s = ΓI i (S.insert (Right n) s)

instance Ord a => L a (Pos a) where
  p <| ΓI i s = ΓI (S.insert p i) s

minInvertibleL :: Ord a => ΓI a -> Either (Γ (Either a (Neg a))) (Pos a, ΓI a)
minInvertibleL (ΓI i s) = maybe (Left s) (\ (p, i') -> Right (p, ΓI i' s)) (S.minView i)

type ΓS a = S.Multiset (Either a (Neg a))


data ΔI a = ΔI
  (ΔS a)
  (S.Multiset (Neg a))

class Ord a => R a p where
  (|>) :: ΔI a -> p -> ΔI a
  infixl 5 |>

instance Ord a => R a a where
  ΔI s i |> a = ΔI (S.insert (Right a) s) i

instance Ord a => R a (Neg a) where
  ΔI s i |> n = ΔI s (S.insert n i)

instance Ord a => R a (Pos a) where
  ΔI s i |> p = ΔI (S.insert (Left p) s) i

minInvertibleR :: Ord a => ΔI a -> Either (Δ (Either (Pos a) a)) (ΔI a, Neg a)
minInvertibleR (ΔI s i) = maybe (Left s) (\ (n, i') -> Right (ΔI s i', n)) (S.minView i)

type ΔS a = S.Multiset (Either (Pos a) a)


class Sequent l r where
  (|-) :: (Alternative m, Monad m) => l -> r -> m ()
  infix 4 |-

instance Ord a => Sequent (ΓI a) (ΔI a) where
  _Γ |- _Δ = case (minInvertibleL _Γ, minInvertibleR _Δ) of
    (Left  _Γ,      Left  _Δ)      -> _Γ |- _Δ
    (Right (p, _Γ), _)             -> case p of
      P a      -> a <| _Γ |- _Δ
      Zero     -> pure ()
      One      -> _Γ |- _Δ
      p :+: q  -> p <| _Γ |- _Δ >> q <| _Γ |- _Δ
      p :*: q  -> p <| q <| _Γ |- _Δ
      p :-<: q -> p <| _Γ |- _Δ |> q
      Inv p    -> _Γ |- _Δ |> p
      Down p   -> p <| _Γ |- _Δ
    (_,             Right (_Δ, n)) -> case n of
      N a      -> _Γ |- _Δ |> a
      Bot      -> _Γ |- _Δ
      Top      -> pure ()
      p :⅋: q  -> _Γ |- _Δ |> p |> q
      p :&: q  -> (_Γ |- _Δ |> p) >> _Γ |- _Δ |> q
      p :->: q -> p <| _Γ |- _Δ |> q
      Not p    -> p <| _Γ |- _Δ
      Up p     -> _Γ |- _Δ |> p

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
    N a      -> guard (Right a `elem` _Δ)
    Bot      -> pure ()
    Top      -> empty -- no left rule for ⊤
    p :⅋: q  -> p :<: _Γ |- _Δ <|> q :<: _Γ |- _Δ
    p :&: q  -> p :<: _Γ |- _Δ >> q :<: _Γ |- _Δ
    p :->: q -> _Γ |- _Δ :>: p >> q :<: _Γ |- _Δ
    Not p    -> ΓI mempty _Γ |- ΔI _Δ (S.singleton p)
    Up p     -> ΓI (S.singleton p) _Γ |- ΔI _Δ mempty

instance Ord a => Sequent (ΓS a) (ΔS a :>: Pos a) where
  _Γ |- _Δ :>: p = case p of
    P a      -> guard (Left a `elem` _Γ)
    Zero     -> empty -- no right rule for 0
    One      -> pure ()
    p :+: q  -> _Γ |- _Δ :>: p <|> _Γ |- _Δ :>: q
    p :*: q  -> _Γ |- _Δ :>: p >> _Γ |- _Δ :>: q
    p :-<: q -> _Γ |- _Δ :>: p >> q :<: _Γ |- _Δ
    Inv p    -> ΓI (S.singleton p) _Γ |- ΔI _Δ mempty
    Down p   -> ΓI mempty _Γ |- ΔI _Δ (S.singleton p)
