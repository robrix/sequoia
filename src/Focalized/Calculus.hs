{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( Core(..)
, Structural(..)
, Negative(..)
, Additive(..)
, Multiplicative(..)
, Implicative(..)
, Γ(..)
, Δ
) where

import Control.Applicative (liftA2)
import Control.Monad (ap, join)
import Data.Bifoldable
import Data.Bifunctor (Bifunctor(..))
import Data.Bitraversable
import Prelude hiding (init, tail)

type (|>) = Either
infixl 4 |>

split :: (_Δ |> a -> r) -> (_Δ -> r, a -> r)
split f = (f . Left, f . Right)


data a ⊗ b = !a :⊗ !b

infixr 7 ⊗

instance Bifoldable (⊗) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⊗) where
  bimap = bimapDefault

instance Bitraversable (⊗) where
  bitraverse f g (a :⊗ b) = inlr <$> f a <*> g b

newtype a & b = With (forall r . (a -> b -> r) -> r)

infixr 6 &

instance Bifoldable (&) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (&) where
  bimap = bimapDefault

instance Bitraversable (&) where
  bitraverse f g w = inlr <$> f (exl w) <*> g (exr w)

class Conj c where
  inlr :: a -> b -> a `c` b
  exl :: a `c` b -> a
  exr :: a `c` b -> b

instance Conj (⊗) where
  inlr = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r

instance Conj (&) where
  inlr a b = With $ \ f -> f a b
  exl (With run) = run const
  exr (With run) = run (const id)

data a ⊕ b
  = InL !a
  | InR !b

infixr 6 ⊕

instance Bifoldable (⊕) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⊕) where
  bimap = bimapDefault

instance Bitraversable (⊕) where
  bitraverse f g = \case
    InL a -> InL <$> f a
    InR b -> InR <$> g b

newtype (a ⅋ b) = Par (forall r . (a -> r) -> (b -> r) -> r)

infixr 7 ⅋

instance Bifoldable (⅋) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⅋) where
  bimap = bimapDefault

instance Bitraversable (⅋) where
  bitraverse f g (Par run) = run (fmap inl . f) (fmap inr . g)

class Disj d where
  inl :: a -> a `d` b
  inr :: b -> a `d` b
  exlr :: (a -> r) -> (b -> r) -> a `d` b -> r

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

newtype a --> b = Fun { appFun :: (b -> Δ) -> (a -> Δ) }

infixr 5 -->

data a --< b = Sub { subA :: !a, subK :: !(Negate b) }

infixr 5 --<

newtype Not    a = Not    { runNot    :: a -> Δ }
newtype Negate a = Negate { runNegate :: a -> Δ }

data Bot
data Top = Top

data Zero
data One = One


data Γ = Γ
data Δ


class Core p where
  (>>>) :: _Γ `p` (_Δ |> a) -> (a, _Γ) `p` _Δ -> _Γ `p` _Δ

  init :: (a, _Γ) `p` (_Δ |> a)


infixr 1 >>>


class Structural p where
  -- | Pop something off the input context which can later be pushed. Used with 'pushL', this provides a generalized context restructuring facility.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  popL :: (a -> _Γ `p` _Δ) -> (a, _Γ) `p` _Δ

  -- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL :: (a, _Γ) `p` _Δ -> a -> _Γ `p` _Δ

  popL2 :: (a -> b -> _Γ `p` _Δ) -> (a, (b, _Γ)) `p` _Δ
  popL2 f = popL (popL . f)

  pushL2 :: (a, (b, _Γ)) `p` _Δ -> a -> b -> _Γ `p` _Δ
  pushL2 p = pushL . pushL p


  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR :: ((a -> Δ) -> _Γ `p` _Δ) -> _Γ `p` (_Δ |> a)

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR :: _Γ `p` (_Δ |> a) -> ((a -> Δ) -> _Γ `p` _Δ)

  popR2 :: ((a -> Δ) -> (b -> Δ) -> _Γ `p` _Δ) -> _Γ `p` (_Δ |> b |> a)
  popR2 f = popR (popR . f)

  pushR2 :: _Γ `p` (_Δ |> b |> a) -> (a -> Δ) -> (b -> Δ) -> _Γ `p` _Δ
  pushR2 p = pushR . pushR p


  wkL :: _Γ `p` _Δ -> (a, _Γ) `p` _Δ
  wkL = popL . const
  wkR :: _Γ `p` _Δ -> _Γ `p` (_Δ |> a)
  wkR = popR . const
  cnL :: (a, (a, _Γ)) `p` _Δ -> (a, _Γ) `p` _Δ
  cnL = popL . join . pushL2
  cnR :: _Γ `p` (_Δ |> a |> a) -> _Γ `p` (_Δ |> a)
  cnR = popR . join . pushR2
  exL :: (a, (b, c)) `p` _Δ -> (b, (a, c)) `p` _Δ
  exL = popL2 . flip . pushL2
  exR :: _Γ `p` (_Δ |> a |> b) -> _Γ `p` (_Δ |> b |> a)
  exR = popR2 . flip . pushR2


class (Core p, Structural p) => Negative p where
  negateL :: _Γ `p` (_Δ |> a) -> (Negate a, _Γ) `p` _Δ
  negateL' :: (Negate a, _Γ) `p` _Δ -> _Γ `p` (_Δ |> a)
  negateL' p = negateR init >>> wkR p
  negateR :: (a, _Γ) `p` _Δ -> _Γ `p` (_Δ |> Negate a)
  negateR' :: _Γ `p` (_Δ |> Negate a) -> (a, _Γ) `p` _Δ
  negateR' p = wkL p >>> negateL init

  notL :: _Γ `p` (_Δ |> a) -> (Not a, _Γ) `p` _Δ
  notL' :: (Not a, _Γ) `p` _Δ -> _Γ `p` (_Δ |> a)
  notL' p = notR init >>> wkR p
  notR :: (a, _Γ) `p` _Δ -> _Γ `p` (_Δ |> Not a)
  notR' :: _Γ `p` (_Δ |> Not a) -> (a, _Γ) `p` _Δ
  notR' p = wkL p >>> notL init


class (Core p, Structural p, Negative p) => Additive p where
  zeroL :: (Zero, _Γ) `p` _Δ

  topR :: _Γ `p` (_Δ |> Top)

  sumL :: (a, _Γ) `p` _Δ -> (b, _Γ) `p` _Δ -> (a ⊕ b, _Γ) `p` _Δ
  sumL p1 p2 = sumLWith (notR p1 & notR p2)
  sumL1' :: (a ⊕ b, _Γ) `p` _Δ -> (a, _Γ) `p` _Δ
  sumL1' p = sumR1 init >>> exL (wkL p)
  sumL2' :: (a ⊕ b, _Γ) `p` _Δ -> (b, _Γ) `p` _Δ
  sumL2' p = sumR2 init >>> exL (wkL p)
  sumLWith :: _Γ `p` (_Δ |> Not a & Not b) -> (a ⊕ b, _Γ) `p` _Δ
  sumLWith p = wkL p >>> exL (sumL (exL (withL1 (notL init))) (exL (withL2 (notL init))))
  sumR1 :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> a ⊕ b)
  sumR2 :: _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a ⊕ b)

  withL1 :: (a, _Γ) `p` _Δ -> (a & b, _Γ) `p` _Δ
  withL1 = withLSum . sumR1 . negateR
  withL2 :: (b, _Γ) `p` _Δ -> (a & b, _Γ) `p` _Δ
  withL2 = withLSum . sumR2 . negateR
  withLSum :: _Γ `p` (_Δ |> Negate a ⊕ Negate b) -> (a & b, _Γ) `p` _Δ
  withLSum p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
  (&) :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a & b)
  withR1' :: _Γ `p` (_Δ |> a & b) -> _Γ `p` (_Δ |> a)
  withR1' t = exR (wkR t) >>> withL1 init
  withR2' :: _Γ `p` (_Δ |> a & b) -> _Γ `p` (_Δ |> b)
  withR2' t = exR (wkR t) >>> withL2 init

  zapSum :: _Γ `p` (_Δ |> Not a & Not b) -> (a ⊕ b, _Γ) `p` _Δ
  zapSum p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))

  zapWith :: _Γ `p` (_Δ |> Negate a ⊕ Negate b) -> (a & b, _Γ) `p` _Δ
  zapWith p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))


class (Core p, Structural p, Negative p) => Multiplicative p where
  botL :: (Bot, _Γ) `p` _Δ
  botR :: _Γ `p` _Δ -> _Γ `p` (_Δ |> Bot)
  botR' :: _Γ `p` (_Δ |> Bot) -> _Γ `p` _Δ
  botR' = (>>> botL)

  oneL :: _Γ `p` _Δ -> (One, _Γ) `p` _Δ
  oneL' :: (One, _Γ) `p` _Δ -> _Γ `p` _Δ
  oneL' = (oneR >>>)
  oneR :: _Γ `p` (_Δ |> One)

  parL :: (a, _Γ) `p` _Δ -> (b, _Γ) `p` _Δ -> (a ⅋ b, _Γ) `p` _Δ
  parL p1 p2 = parLTensor (negateR p1 ⊗ negateR p2)
  parLTensor :: _Γ `p` (_Δ |> Negate a ⊗ Negate b) -> (a ⅋ b, _Γ) `p` _Δ
  parLTensor p = wkL p >>> tensorL (negateL (negateL (parL (wkR init) init)))
  parR :: _Γ `p` (_Δ |> a |> b) -> _Γ `p` (_Δ |> a ⅋ b)
  parR' :: _Γ `p` (_Δ |> a ⅋ b) -> _Γ `p` (_Δ |> a |> b)
  parR' p = exR (wkR (exR (wkR p))) >>> parL (wkR init) init

  tensorL :: (a, (b, _Γ)) `p` _Δ -> (a ⊗ b, _Γ) `p` _Δ
  tensorL = tensorLPar . parR . notR . notR
  tensorLPar :: _Γ `p` (_Δ |> Not a ⅋ Not b) -> (a ⊗ b, _Γ) `p` _Δ
  tensorLPar p = wkL p >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
  tensorL' :: (a ⊗ b, _Γ) `p` _Δ -> (a, (b, _Γ)) `p` _Δ
  tensorL' p = init ⊗ wkL init >>> popL (wkL . wkL . pushL p)
  (⊗) :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a ⊗ b)

  zapTensor :: _Γ `p` (_Δ |> Not a ⅋ Not b) -> (a ⊗ b, _Γ) `p` _Δ
  zapTensor p = tensorL (wkL (wkL p) >>> parL (notL init) (notL (wkL init)))

  zapPar :: _Γ `p` (_Δ |> Negate a ⊗ Negate b) -> (a ⅋ b, _Γ) `p` _Δ
  zapPar p = wkL p >>> tensorL (popL2 (parL `on0` pushL (negateL init) `on1` pushL (negateL init)))


class (Core p, Structural p, Negative p) => Implicative p where
  funL :: _Γ `p` (_Δ |> a) -> (b, _Γ) `p` _Δ -> (a --> b, _Γ) `p` _Δ
  funL pa pb = funLSub (subR pa pb)
  funLSub :: _Γ `p` (_Δ |> a --< b) -> (a --> b, _Γ) `p` _Δ
  funLSub p = wkL p >>> subL (exL (funL init init))
  funL2 :: (a --> b, (a, _Γ)) `p` (_Δ |> b)
  funL2 = funL init init
  funR :: (a, _Γ) `p` (_Δ |> b) -> _Γ `p` (_Δ |> a --> b)
  funR' :: _Γ `p` (_Δ |> a --> b) -> (a, _Γ) `p` (_Δ |> b)
  funR' p = wkL (exR (wkR p)) >>> funL2

  subL :: (a, _Γ) `p` (_Δ |> b) -> (a --< b, _Γ) `p` _Δ
  subL = subLFun . funR
  subLFun :: _Γ `p` (_Δ |> a --> b) -> (a --< b, _Γ) `p` _Δ
  subLFun p = wkL p >>> exL (subL (exL (funL init init)))
  subL' :: (a --< b, _Γ) `p` _Δ -> (a, _Γ) `p` (_Δ |> b)
  subL' p = subR init init >>> wkR (exL (wkL p))
  subR :: _Γ `p` (_Δ |> a) -> (b, _Γ) `p` _Δ -> _Γ `p` (_Δ |> a --< b)

  ($$) :: _Γ `p` (_Δ |> a --> b) -> _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b)
  f $$ a = exR (wkR f) >>> exR (wkR a) `funL` init

on0 :: (a -> b -> c) -> (a' -> a) -> (a' -> b -> c)
on0 = (.)

on1 :: (a -> b -> c) -> (b' -> b) -> (a -> b' -> c)
on1 = fmap flip . (.) . flip

infixl 4 `on0`, `on1`


newtype _Γ |- _Δ = Seq ((_Δ -> Δ) -> (_Γ -> Δ))
  deriving (Functor)

infix 2 |-

appSeq :: (_Δ -> Δ) -> _Γ -> _Γ |- _Δ -> Δ
appSeq k c (Seq run) = run k c

instance Applicative ((|-) _Γ) where
  pure a = Seq $ \ k _ -> k a
  (<*>) = ap

instance Monad ((|-) _Γ) where
  Seq a >>= f = Seq $ \ k c -> a (appSeq k c . f) c


instance Core (|-) where
  f >>> g = f >>= either pure (pushL g)

  init = popL (pure . pure)

instance Structural (|-) where
  popL f = Seq $ \ k -> uncurry (flip (appSeq k) . f)
  pushL (Seq run) a = Seq $ \ k -> run k . (a,)

  popR f = Seq $ \ k c -> let (k', ka) = split k in appSeq k' c (f ka)
  pushR (Seq run) a = Seq $ \ k -> run (either k a)

instance Negative (|-) where
  negateL (Seq run) = Seq $ \ k (negA, c) -> run (either k (runNegate negA)) c
  negateR (Seq run) = Seq $ \ k c -> let (k', ka) = split k in ka (Negate (run k' . (,c)))

  notL (Seq run) = Seq $ \ k (notA, c) -> run (either k (runNot notA)) c
  notR (Seq run) = Seq $ \ k c -> let (k', ka) = split k in ka (Not (run k' . (,c)))

instance Additive (|-) where
  zeroL = popL absurdP

  topR = pure (pure Top)

  sumL a b = popL (exlr (pushL a) (pushL b))
  sumR1 = fmap (fmap inl)
  sumR2 = fmap (fmap inr)

  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  (&) = liftA2 (liftA2 inlr)

instance Multiplicative (|-) where
  botL = popL absurdN
  botR = fmap Left

  oneL = wkL
  oneR = pure (pure One)

  parL a b = popL (exlr (pushL a) (pushL b))
  parR ab = either (>>= (pure . inl)) (pure . inr) <$> ab

  tensorL p = popL (pushL2 p . exl <*> exr)
  (⊗) = liftA2 (liftA2 inlr)

instance Implicative (|-) where
  funL a b = popL (\ f -> a >>> Seq (\ k (a, _Γ) -> appFun f (appSeq k _Γ . pushL b) a))
  funR (Seq run) = Seq $ \ k c -> let (k', ka) = split k in ka (Fun (\ kb -> run (either k' kb) . (,c)))

  subL b = popL (\ s -> pushL b (subA s) >>> pushL (negateL init) (subK s))
  subR a b = liftA2 Sub <$> a <*> negateR b


absurdN :: Bot -> a
absurdN = \case

absurdP :: Zero -> a
absurdP = \case
