{-# LANGUAGE FunctionalDependencies #-}
module Focalized.Calculus
( Proof(..)
) where

import Control.Applicative (liftA2)
import Control.Monad (join)
import Prelude hiding (tail)

type (<|) = (,)
infixr 5 <|
type (|>) = Either
infixl 5 |>

type (|-) = (->)

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

class Proof p where
  withL1 :: (a <| _Γ) `p` _Δ -> (a & b <| _Γ) `p` _Δ
  withL2 :: (b <| _Γ) `p` _Δ -> (a & b <| _Γ) `p` _Δ
  (&) :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a & b)

  tensorL :: (a <| b <| _Γ) `p` _Δ -> (a ⊗ b <| _Γ) `p` _Δ
  (⊗) :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a ⊗ b)

  sumL :: (a <| _Γ) `p` _Δ -> (b <| _Γ) `p` _Δ -> (a ⊕ b <| _Γ) `p` _Δ
  sumR1 :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> a ⊕ b)
  sumR2 :: _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a ⊕ b)

  parL :: (a <| _Γ) `p` _Δ -> (b <| _Γ) `p` _Δ -> (a ⅋ b <| _Γ) `p` _Δ
  parR :: _Γ `p` (_Δ |> a |> b) -> _Γ `p` (_Δ |> a ⅋ b)

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
  withL1 p (with, _Γ) = p (exl with, _Γ)
  withL2 p (with, _Γ) = p (exr with, _Γ)
  (&) = liftA2 (liftA2 inlr)

  tensorL p (a :⊗ b, _Γ) = p (a, (b, _Γ))
  (⊗) = liftA2 (liftA2 inlr)

  sumL a b (sum, _Γ) = exlr (a . (,_Γ)) (b . (,_Γ)) sum
  sumR1 a = fmap inl <$> a
  sumR2 b = fmap inr <$> b

  parL a b (sum, _Γ) = exlr (a . (,_Γ)) (b . (,_Γ)) sum
  parR ab = either (>>= (pure . inl)) (pure . inr) . ab

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
