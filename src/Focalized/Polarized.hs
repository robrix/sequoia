{-# LANGUAGE FunctionalDependencies #-}
module Focalized.Polarized
( Neg(..)
, CBN(..)
, ECBN(..)
, ICBN(..)
, evalN
, Pos(..)
, CBV(..)
, ECBV(..)
, ICBV(..)
, evalV
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
import           Focalized.Snoc as Snoc

data a :|-: b = a :|-: b

infix 4 :|-:


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

data CBN a
  = Covar a
  | ECBN (ECBN a)
  | ICBN (ICBN a)

data ECBN a
  = EBot (CBN a) -- Bot L
  -- no rule for Top L
  | EWithL (CBN a) -- :&: L₁
  | EWithR (CBN a) -- :&: L₂
  | EPar (CBN a) (CBN a) (CBN a) -- :⅋: L
  | ELam (CBN a) (CBV a) -- :->: L
  | ENot (CBN a) -- Not L
  | EThunk (CBV a) -- Down L

data ICBN a
  = IBot -- Bot R
  | ITop -- Top R
  | IWith (CBN a) (CBN a) -- :&: R
  | IPar (CBN a -> CBN a -> CBN a) -- :⅋: R
  | ILam (CBV a -> CBN a) -- :->: R
  | INot (CBN a) -- Not R
  | IReturn (CBV a) -- Up R

evalN :: Eq a => Snoc (a, CBV a) :|-: [(a, CBN a)] -> CBN a -> [ICBN a]
evalN env@(_Γ :|-: _Δ) = \case
  Covar a -> case Prelude.lookup a _Δ of
    Just e  -> evalN env e
    Nothing -> []
  ECBN e  -> case e of
    EBot e   -> evalN env e
    EWithL l -> do
      IWith l' _ <- evalN env l
      evalN env l'
    EWithR r -> do
      IWith r' _ <- evalN env r
      evalN env r'
    EPar p a b -> do
      IPar f <- evalN env p
      evalN env (f a b)
    ELam f a -> do
      ILam b <- evalN env f
      evalN env (b a)
    ENot e   -> do
      INot e' <- evalN env e
      evalN env e'
    EThunk t -> do
      IThunk e <- evalV env t
      evalN env e
  ICBN i  -> [i]


data Pos a
  = P a
  | Zero
  | One
  | Pos a :+: Pos a
  | Pos a :*: Pos a
  | Pos a :-<: Neg a
  | Neg (Pos a)
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
    Neg a    -> Neg (a >>= f)
    Down a   -> Down (a >>= Up . f)

data CBV a
  = Var a
  | ECBV (ECBV a)
  | ICBV (ICBV a)

data ECBV a
  = EZero (CBV a) -- Zero L
  -- no rule for Zero R
  | EOne (CBV a) -- One L
  | ESum (CBV a) (ICBV a -> CBV a) (ICBV a -> CBV a) -- :+: L
  | EPair (CBV a) (ICBV a -> ICBV a -> CBV a) -- :*: L
  | EColam (CBV a) (ICBV a -> CBN a) -- :-<: L
  | ENeg (CBV a) -- Neg L
  | EReturn (CBN a) -- Up L

data ICBV a
  = IOne -- One R
  | ISumL (ICBV a) -- :+: R₁
  | ISumR (ICBV a) -- :+: R₂
  | IPair (ICBV a) (ICBV a) -- :*: R
  | IColam (ICBV a) -- :-<: R -- FIXME: should this be in CBN?
  | INeg (ICBV a) -- Neg R
  | IThunk (CBN a) -- Down R

evalV :: Eq a => Snoc (a, CBV a) :|-: [(a, CBN a)] -> CBV a -> [ICBV a]
evalV env@(_Γ :|-: _Δ) = \case
  Var a -> case Snoc.lookup a _Γ of
    Just e  -> evalV env e
    Nothing -> []
  ECBV e -> case e of
    EZero e    -> evalV env e
    EOne e     -> evalV env e
    ESum s f g -> do
      s' <- evalV env s
      case s' of
        ISumL l -> evalV env (f l)
        ISumR r -> evalV env (g r)
        _       -> []
    EPair s f -> do
      IPair l r <- evalV env s
      evalV env (f l r)
    EColam s b -> do
      IColam a <- evalV env s
      IThunk . ICBN <$> evalN env (b a)
    ENeg e -> do
      INeg e' <- evalV env e
      [e']
    EReturn e -> do -- this isn’t really how return works in e.g. CBPV, so this is probably a bad name
      IReturn e' <- evalN env e
      evalV env e'
  ICBV i -> [i]


type Γ = S.Multiset
type Δ = S.Multiset

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

minInvertibleL :: Ord a => ΓI a -> Either (Γ (Either a (Neg a))) (Pos a, ΓI a)
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

minInvertibleR :: Ord a => ΔI a -> Either (Δ (Either (Pos a) a)) (ΔI a, Neg a)
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
      P a      -> a <| _Γ |- _Δ
      Zero     -> pure ()
      One      -> _Γ |- _Δ
      p :+: q  -> p <| _Γ |- _Δ >> q <| _Γ |- _Δ
      p :*: q  -> p <| q <| _Γ |- _Δ
      p :-<: q -> p <| _Γ |- _Δ |> q
      Neg p    -> _Γ |- _Δ |> p
      Down p   -> p <| _Γ |- _Δ
    (_,             Right (_Δ, n)) -> case n of
      N a      -> _Γ |- _Δ |> a
      Bot      -> _Γ |- _Δ
      Top      -> pure ()
      p :⅋: q  -> _Γ |- _Δ |> p |> q
      p :&: q  -> _Γ |- _Δ |> p >> _Γ |- _Δ |> q
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
    p :⅋: q  -> p :<: _Γ |- _Δ >> q :<: _Γ |- _Δ
    p :&: q  -> p :<: _Γ |- _Δ <|> q :<: _Γ |- _Δ
    p :->: q -> _Γ |- _Δ :>: p >> q :<: _Γ |- _Δ
    Not p    -> _Γ |- _Δ |> p
    Up p     -> p <| _Γ |- _Δ

instance Ord a => Sequent (ΓS a) (ΔS a :>: Pos a) where
  _Γ |- _Δ :>: p = case p of
    P a      -> guard (Left a `elem` _Γ)
    Zero     -> empty -- no right rule for 0
    One      -> pure ()
    p :+: q  -> _Γ |- _Δ :>: p <|> _Γ |- _Δ :>: q
    p :*: q  -> _Γ |- _Δ :>: p >> _Γ |- _Δ :>: q
    p :-<: q -> _Γ |- _Δ :>: p >> q :<: _Γ |- _Δ
    Neg p    -> p <| _Γ |- _Δ
    Down p   -> _Γ |- _Δ |> p
