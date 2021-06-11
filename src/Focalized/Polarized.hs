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
, Proof(..)
) where

import           Control.Applicative (Alternative(..), liftA2)
import           Control.Effect.NonDet (foldMapA, guard)
import           Control.Monad (ap, join)
import qualified Focalized.Multiset as S
import           Prelude hiding (head, tail)

data a ⊗ b = !a :⊗ !b

infixr 7 ⊗

data a & b = a :& b

infixr 6 &

class Conj p where
  inlr :: a -> b -> a `p` b
  exl :: a `p` b -> a
  exr :: a `p` b -> b

instance Conj (⊗) where
  inlr = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r

instance Conj (&) where
  inlr = (:&)
  exl (l :& _) = l
  exr (_ :& r) = r

data a ⊕ b
  = InL !a
  | InR !b

infixr 6 ⊕

newtype (a ⅋ b) = Par (forall r . (a -> r) -> (b -> r) -> r)

infixr 7 ⅋

class Disj s where
  inl :: a -> a `s` b
  inr :: b -> a `s` b
  exlr :: (a -> r) -> (b -> r) -> a `s` b -> r

instance Disj (⊕) where
  inl = InL
  inr = InR
  exlr ifl ifr = \case
    InL l -> ifl l
    InR r -> ifr r

instance Disj (⅋) where
  inl l = Par $ \ ifl _ -> ifl l
  inr r = Par $ \ _ ifr -> ifr r
  exlr ifl ifr (Par run) = run ifl ifr

newtype (a --> b) _Δ = Fun { getFun :: a -> (_Δ |> b) }

infixr 0 -->

data (a --< b) _Δ = Sub a (Cont b _Δ)

infixr 0 --<

type Not = Cont
type Negate = (--<) One

newtype Cont a _Δ = Cont { runCont :: a -> _Δ }

data Bot
data Top = Top'

data Zero
data One = One'


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

type (<|) = (,)
type (|>) = Either
type (|-) = (->)

class Proof p where
  (&) :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a & b)

  (⊗) :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a ⊗ b)

  sumL :: (a <| _Γ) `p` _Δ -> (b <| _Γ) `p` _Δ -> (a ⊕ b <| _Γ) `p` _Δ
  sumR1 :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> a ⊕ b)
  sumR2 :: _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a ⊕ b)

  funL :: _Γ `p` (_Δ |> a) -> (b <| _Γ) `p` _Δ -> ((a --> b) _Δ <| _Γ) `p` _Δ
  funR :: (a <| _Γ) `p` (_Δ |> b) -> _Γ `p` (_Δ |> (a --> b) _Δ)

  subL :: (a <| _Γ) `p` (_Δ |> b) -> ((a --< b) _Δ <| _Γ) `p` _Δ
  subR :: _Γ `p` (_Δ |> a) -> (b <| _Γ) `p` _Δ -> _Γ `p` (_Δ |> (a --< b) _Δ)

  ($$) :: _Γ `p` (_Δ |> (a --> b) (_Δ |> b)) -> _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b)
  f $$ a = cut (exR (wkR f)) (exR (wkR a) `funL` ax)

  zeroL :: (Zero <| _Γ) `p` _Δ

  oneL :: _Γ `p` _Δ -> (One <| _Γ) `p` _Δ
  oneR :: _Γ `p` (_Δ |> One)

  botL :: (Bot <| _Γ) `p` _Δ
  botR :: _Γ `p` _Δ -> _Γ `p` (_Δ |> Bot)

  topR :: _Γ `p` (_Δ |> Top)

  negateL :: _Γ `p` (_Δ |> a) -> (Negate a _Δ <| _Γ) `p` _Δ
  negateR :: (a <| _Γ) `p` _Δ -> _Γ `p` (_Δ |> Negate a _Δ)

  notL :: _Γ `p` (_Δ |> a) -> (Not a _Δ <| _Γ) `p` _Δ
  notR :: (a <| _Γ) `p` _Δ -> _Γ `p` (_Δ |> Not a _Δ)

  cut :: _Γ `p` (_Δ |> a) -> (a <| _Γ) `p` _Δ -> _Γ `p` _Δ

  ax :: (a, _Γ) `p` (_Δ |> a)

  wkL :: _Γ `p` _Δ -> (a <| _Γ) `p` _Δ
  wkR :: _Γ `p` _Δ -> _Γ `p` (_Δ |> a)
  cnL :: (a <| a) `p` b -> a `p` b
  cnR :: _Γ `p` (a |> a) -> _Γ `p` a
  exL :: (a <| b <| c) `p` _Δ -> (b <| a <| c) `p` _Δ
  exR :: _Γ `p` (a |> b |> c) -> _Γ `p` (a |> c |> b)


  zapSum :: _Γ `p` (_Δ |> Not a _Δ & Not b _Δ) -> (a ⊕ b <| _Γ) `p` _Δ


instance Proof (|-) where
  (&) = liftA2 (liftA2 inlr)

  (⊗) = liftA2 (liftA2 inlr)

  sumL a b (sum, _Γ) = exlr (a . (,_Γ)) (b . (,_Γ)) sum
  sumR1 a = fmap inl <$> a
  sumR2 b = fmap inr <$> b

  funL a kb (f, _Γ) = a _Γ >>- \ a' -> getFun f a' >>- \ b' -> kb (b', _Γ)
  funR p _Γ = Right $ Fun $ \ a -> p (a, _Γ)

  subL b (Sub a k, _Γ) = notL (b . (a,)) (k, _Γ)
  subR a b = liftA2 Sub <$> a <*> notR b

  zeroL = absurdP . fst

  oneL = wkL
  oneR = const (pure One')

  botL = absurdN . fst
  botR = fmap Left

  topR = const (pure Top')

  notL p (k, _Γ) = p _Γ >>- runCont k
  notR p _Γ = Right $ Cont $ \ a -> p (a, _Γ)

  negateL = subL . wkL
  negateR = subR oneR

  cut f g _Γ = f _Γ >>- \ a -> g (a, _Γ)

  ax = Right . fst

  wkL = (. snd)
  wkR = fmap Left
  cnL = (. join (,))
  cnR = fmap (either id id)
  exL = (. \ (b, (a, c)) -> (a, (b, c)))
  exR = fmap (either (either (Left . Left) Right) (Left . Right))

  zapSum elim = tail elim >>= \ _Δ (sum, _) -> _Δ >>- flip zap sum


tail :: Proof p => _Γ' `p` _Δ -> (_Γ, _Γ') `p` _Δ
tail = wkL

absurdN :: Bot -> a
absurdN = \case

absurdP :: Zero -> a
absurdP = \case

(>>-) :: (_Δ |> a) -> (a -> _Δ) -> _Δ
(>>-) = flip (either id)

infixl 1 >>-

(|||) :: (a -> c) -> (b -> c) -> (a ⊕ b) -> c
f ||| g = \case
  InL a -> f a
  InR b -> g b

infixr 2 |||

class Zap a b c | a b -> c, b c -> a, a c -> b where
  zap :: a -> b -> c

instance Zap (Not a _Δ & Not b _Δ) (a ⊕ b) _Δ where
  zap (f :& g) = runCont f ||| runCont g
