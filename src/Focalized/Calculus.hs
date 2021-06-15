{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( Core(..)
, Structural(..)
, Negative(..)
, Additive(..)
, Proof(..)
, Γ(..)
, Δ
) where

import Control.Applicative (liftA2)
import Control.Category (Category)
import Control.Monad (join)
import Data.Bifoldable
import Data.Bifunctor (Bifunctor(..))
import Data.Bitraversable
import Data.Profunctor
import Prelude hiding (init, tail)

type (|>) = Either
infixl 4 |>

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

newtype a --> b = Fun { appFun :: forall _Δ . a -> (_Δ |> b) }

infixr 5 -->

data (a --< b) _Δ = Sub { subA :: !a, subK :: !(Negate b _Δ) }

infixr 5 --<

type Not = (->)
type Negate = (->)

data Bot
data Top = Top

data Zero
data One = One


data Γ = Γ
data Δ

absurdΔ :: Δ -> a
absurdΔ = \case

-- | Append a value to an output. For exclusive choice–based outputs, this should replace its second argument with its first. For inclusive choice, it should be a true append.
(|>) :: _Δ -> a -> _Δ |> a
(|>) = const pure


class Profunctor p => Core p where
  cut :: _Γ `p` (_Δ |> a) -> (a, _Γ) `p` _Δ -> _Γ `p` _Δ

  infixr 2 `cut`

  init :: (a, _Γ) `p` (_Δ |> a)


class Profunctor p => Structural p where
  -- | Pop something off the context which can later be pushed. Used with 'pushL', this provides a generalized context reordering facility.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  popL :: (a -> _Γ `p` _Δ) -> (a, _Γ) `p` _Δ

  -- | Push something onto the context which was previously popped off it. Used with 'popL', this provides a generalized context reordering facility. It is undefined what will happen if you push something which was not previously popped.
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

  popR :: _Γ `p` (_Δ |> a) -> (a -> _Γ `p` _Δ) -> _Γ `p` _Δ
  pushR :: _Γ `p` _Δ -> (_Δ -> _Δ |> a) -> _Γ `p` (_Δ |> a)
  pushR = flip rmap

  popR2 :: _Γ `p` (_Δ |> a |> b) -> (Either a b -> _Γ `p` _Δ) -> _Γ `p` _Δ
  popR2 p k = popR (popR p (wkR . k . Right)) (k . Left)

  pushR2 :: _Γ `p` _Δ -> Either a b -> _Γ `p` (_Δ |> a |> b)
  pushR2 p = either (wkR . pushR p . flip (|>)) (pushR (wkR p) . flip (|>))


  wkL :: _Γ `p` _Δ -> (a, _Γ) `p` _Δ
  wkL = popL . const
  wkR :: _Γ `p` _Δ -> _Γ `p` (_Δ |> a)
  wkR = (`pushR` Left)
  cnL :: (a, (a, _Γ)) `p` _Δ -> (a, _Γ) `p` _Δ
  cnL = popL . join . pushL2
  cnR :: _Γ `p` (_Δ |> a |> a) -> _Γ `p` (_Δ |> a)
  cnR = rmap (either id pure)
  exL :: (a, (b, c)) `p` _Δ -> (b, (a, c)) `p` _Δ
  exL = popL2 . flip . pushL2
  exR :: _Γ `p` (_Δ |> a |> b) -> _Γ `p` (_Δ |> b |> a)
  exR = rmap (either (either (Left . Left) Right) (Left . Right))


class (Core p, Structural p) => Negative p where
  negateL :: _Γ `p` (_Δ |> a) -> (Negate a _Δ, _Γ) `p` _Δ
  negateL' :: (Negate a (_Δ |> a), _Γ) `p` _Δ -> _Γ `p` (_Δ |> a)
  negateL' = cut (negateR init) . wkR
  negateR :: (a, _Γ) `p` _Δ -> _Γ `p` (_Δ |> Negate a _Δ)
  negateR' :: _Γ `p` (_Δ |> Negate a _Δ) -> (a, _Γ) `p` _Δ
  negateR' p = cut (wkL p) (negateL init)

  notL :: _Γ `p` (_Δ |> a) -> (Not a _Δ, _Γ) `p` _Δ
  notL' :: (Not a (_Δ |> a), _Γ) `p` _Δ -> _Γ `p` (_Δ |> a)
  notL' = cut (notR init) . wkR
  notR :: (a, _Γ) `p` _Δ -> _Γ `p` (_Δ |> Not a _Δ)
  notR' :: _Γ `p` (_Δ |> Not a _Δ) -> (a, _Γ) `p` _Δ
  notR' p = cut (wkL p) (notL init)


class (Core p, Structural p, Negative p) => Additive p where
  zeroL :: (Zero, _Γ) `p` _Δ

  topR :: _Γ `p` (_Δ |> Top)

  sumL :: (a, _Γ) `p` _Δ -> (b, _Γ) `p` _Δ -> (a ⊕ b, _Γ) `p` _Δ
  sumL1' :: (a ⊕ b, _Γ) `p` _Δ -> (a, _Γ) `p` _Δ
  sumL1' = cut (sumR1 init) . exL . wkL
  sumL2' :: (a ⊕ b, _Γ) `p` _Δ -> (b, _Γ) `p` _Δ
  sumL2' = cut (sumR2 init) . exL . wkL
  sumR1 :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> a ⊕ b)
  sumR2 :: _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a ⊕ b)

  withL1 :: (a, _Γ) `p` _Δ -> (a & b, _Γ) `p` _Δ
  withL1 = withLSum . sumR1 . negateR
  withL2 :: (b, _Γ) `p` _Δ -> (a & b, _Γ) `p` _Δ
  withL2 = withLSum . sumR2 . negateR
  withLSum :: _Γ `p` (_Δ |> Negate a _Δ ⊕ Negate b _Δ) -> (a & b, _Γ) `p` _Δ
  withLSum p = wkL p `cut` sumL (negateL (withL1 init)) (negateL (withL2 init))
  (&) :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a & b)
  withR1' :: _Γ `p` (_Δ |> a & b) -> _Γ `p` (_Δ |> a)
  withR1' t = exR (wkR t) `cut` withL1 init
  withR2' :: _Γ `p` (_Δ |> a & b) -> _Γ `p` (_Δ |> b)
  withR2' t = exR (wkR t) `cut` withL2 init

  zapSum :: _Γ `p` (_Δ |> Not a _Δ & Not b _Δ) -> (a ⊕ b, _Γ) `p` _Δ
  zapSum p = sumL (cut (wkL p) (withL1 (notL init))) (cut (wkL p) (withL2 (notL init)))

  zapWith :: _Γ `p` (_Δ |> Negate a _Δ ⊕ Negate b _Δ) -> (a & b, _Γ) `p` _Δ
  zapWith p = cut (wkL p) (sumL (negateL (withL1 init)) (negateL (withL2 init)))


class (Core p, Structural p, Negative p) => Proof p where
  tensorL :: (a, (b, _Γ)) `p` _Δ -> (a ⊗ b, _Γ) `p` _Δ
  tensorLPar :: _Γ `p` (_Δ |> Negate a _Δ ⅋ Negate b _Δ) -> (a ⊗ b, _Γ) `p` _Δ
  tensorLPar p = wkL p `cut` parL (negateL (tensorL (exL (wkL init)))) (negateL (tensorL (wkL init)))
  tensorL' :: (a ⊗ b, _Γ) `p` _Δ -> (a, (b, _Γ)) `p` _Δ
  tensorL' p = init ⊗ wkL init `cut` popL (wkL . wkL . pushL p)
  (⊗) :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a ⊗ b)

  parL :: (a, _Γ) `p` _Δ -> (b, _Γ) `p` _Δ -> (a ⅋ b, _Γ) `p` _Δ
  parR :: _Γ `p` (_Δ |> a |> b) -> _Γ `p` (_Δ |> a ⅋ b)
  parR' :: _Γ `p` (_Δ |> a ⅋ b) -> _Γ `p` (_Δ |> a |> b)
  parR' p = cut (exR (wkR (exR (wkR p)))) (parL (wkR init) (exR (wkR init)))

  funL :: _Γ `p` (_Δ |> a) -> (b, _Γ) `p` _Δ -> (a --> b, _Γ) `p` _Δ
  funL2 :: (a --> b, (a, _Γ)) `p` (_Δ |> b)
  funL2 = funL (exR (wkR init)) (exL (wkL init))
  funR :: (a, _Γ) `p` (Δ |> b) -> _Γ `p` (_Δ |> a --> b)
  funR' :: _Γ `p` (_Δ |> a --> b) -> (a, _Γ) `p` (_Δ |> b)
  funR' p = cut (wkL (exR (wkR p))) funL2

  subL :: (a, _Γ) `p` (_Δ |> b) -> ((a --< b) _Δ, _Γ) `p` _Δ
  subL' :: ((a --< b) (_Δ |> b), _Γ) `p` _Δ -> (a, _Γ) `p` (_Δ |> b)
  subL' p = cut (subR (exR (wkR init)) (exL (wkL init))) (wkR (exL (wkL p)))
  subR :: _Γ `p` (_Δ |> a) -> (b, _Γ) `p` _Δ -> _Γ `p` (_Δ |> (a --< b) _Δ)

  ($$) :: _Γ `p` (_Δ |> a --> b) -> _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b)
  f $$ a = cut (exR (wkR f)) (exR (wkR a) `funL` init)

  oneL :: _Γ `p` _Δ -> (One, _Γ) `p` _Δ
  oneL' :: (One, _Γ) `p` _Δ -> _Γ `p` _Δ
  oneL' = cut oneR
  oneR :: _Γ `p` (_Δ |> One)

  botL :: (Bot, _Γ) `p` _Δ
  botR :: _Γ `p` _Δ -> _Γ `p` (_Δ |> Bot)
  botR' :: _Γ `p` (_Δ |> Bot) -> _Γ `p` _Δ
  botR' = (`cut` botL)

  zapTensor :: _Γ `p` (_Δ |> Not a _Δ ⅋ Not b _Δ) -> (a ⊗ b, _Γ) `p` _Δ
  zapTensor p = tensorL (cut (wkL (wkL p)) (parL (notL (exL (wkL init))) (notL (wkL init))))

  zapPar :: _Γ `p` (_Δ |> Negate a _Δ ⊗ Negate b _Δ) -> (a ⅋ b, _Γ) `p` _Δ
  zapPar p = cut (wkL p) (tensorL (popL2 (parL `on0` pushL (negateL init) `on1` pushL (negateL init))))

on0 :: (a -> b -> c) -> (a' -> a) -> (a' -> b -> c)
on0 = (.)

on1 :: (a -> b -> c) -> (b' -> b) -> (a -> b' -> c)
on1 = fmap flip . (.) . flip

infixl 4 `on0`, `on1`


newtype _Γ |- _Δ = Sequent { appSequent :: _Γ -> _Δ }
  deriving (Applicative, Category, Choice, Functor, Monad, Profunctor, Strong)

infix 2 |-


instance Core (|-) where
  cut f g = f >>= either pure (pushL g)

  init = popL (pure . pure)

instance Structural (|-) where
  popL f = Sequent (uncurry (appSequent . f))
  pushL p = Sequent . curry (appSequent p)

  popR p k = p >>= either pure k

instance Negative (|-) where
  negateL p = popL (cut p . popL . fmap pure)
  negateR p = closure (\ _Γ -> pure (close _Γ . pushL p))

  notL p = popL (cut p . popL . fmap pure)
  notR p = closure (\ _Γ -> pure (close _Γ . pushL p))

instance Additive (|-) where
  zeroL = popL absurdP

  topR = pure (pure Top)

  sumL a b = popL (exlr (pushL a) (pushL b))
  sumR1 = fmap (fmap inl)
  sumR2 = fmap (fmap inr)

  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  (&) = liftA2 (liftA2 inlr)

instance Proof (|-) where
  tensorL p = popL (pushL2 p . exl <*> exr)
  (⊗) = liftA2 (liftA2 inlr)

  parL a b = popL (exlr (pushL a) (pushL b))
  parR ab = either (>>= (pure . inl)) (pure . inr) <$> ab

  funL a b = popL (\ f -> a `cut` popL (pure . appFun f) `cut` exL (wkL b))
  funR p = closure (\ _Γ -> pure (Fun (close _Γ . pushL (generalizeR p))))

  subL b = popL (\ s -> cut (pushL b (subA s)) (pushL (negateL init) (subK s)))
  subR a b = liftA2 Sub <$> a <*> negateR b

  oneL = wkL
  oneR = pure (pure One)

  botL = popL absurdN
  botR = fmap Left

closure :: (_Γ -> _Δ) -> _Γ |- _Δ
closure = Sequent

close :: _Γ -> _Γ |- _Δ -> _Δ
close = flip appSequent

generalizeR :: _Γ |- (Δ |> a) -> (forall _Δ . _Γ |- (_Δ |> a))
generalizeR = rmap (either absurdΔ pure)


absurdN :: Bot -> a
absurdN = \case

absurdP :: Zero -> a
absurdP = \case
