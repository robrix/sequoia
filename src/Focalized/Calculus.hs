{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( Proof(..)
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
infixl 5 |>

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

newtype (a --> b) _Δ = Fun { appFun :: a -> (_Δ |> b) }

infixr 0 -->

data (a --< b) _Δ = Sub { subA :: !a, subK :: !(Negate b _Δ) }

infixr 0 --<

type Not = (->)
type Negate = (->)

data Bot
data Top = Top

data Zero
data One = One


class Profunctor p => Proof p where
  withL1 :: (a, _Γ) `p` _Δ -> (a & b, _Γ) `p` _Δ
  withL2 :: (b, _Γ) `p` _Δ -> (a & b, _Γ) `p` _Δ
  (&) :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a & b)
  withR1' :: _Γ `p` (_Δ |> a & b) -> _Γ `p` (_Δ |> a)
  withR1' t = exR (wkR t) `cut` withL1 init
  withR2' :: _Γ `p` (_Δ |> a & b) -> _Γ `p` (_Δ |> b)
  withR2' t = exR (wkR t) `cut` withL2 init

  tensorL :: (a, (b, _Γ)) `p` _Δ -> (a ⊗ b, _Γ) `p` _Δ
  tensorL' :: (a ⊗ b, _Γ) `p` _Δ -> (a, (b, _Γ)) `p` _Δ
  tensorL' p = init ⊗ wkL init `cut` popL (wkL . wkL . pushL p)
  (⊗) :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a ⊗ b)

  sumL :: (a, _Γ) `p` _Δ -> (b, _Γ) `p` _Δ -> (a ⊕ b, _Γ) `p` _Δ
  sumL1' :: (a ⊕ b, _Γ) `p` _Δ -> (a, _Γ) `p` _Δ
  sumL1' = cut (sumR1 init) . exL . wkL
  sumL2' :: (a ⊕ b, _Γ) `p` _Δ -> (b, _Γ) `p` _Δ
  sumL2' = cut (sumR2 init) . exL . wkL
  sumR1 :: _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> a ⊕ b)
  sumR2 :: _Γ `p` (_Δ |> b) -> _Γ `p` (_Δ |> a ⊕ b)

  parL :: (a, _Γ) `p` _Δ -> (b, _Γ) `p` _Δ -> (a ⅋ b, _Γ) `p` _Δ
  parR :: _Γ `p` (_Δ |> a |> b) -> _Γ `p` (_Δ |> a ⅋ b)
  parR' :: _Γ `p` (_Δ |> a ⅋ b) -> _Γ `p` (_Δ |> a |> b)
  parR' p = cut (exR (wkR (exR (wkR p)))) (parL (wkR init) (exR (wkR init)))

  funL :: _Γ `p` (_Δ |> a) -> (b, _Γ) `p` _Δ -> ((a --> b) _Δ, _Γ) `p` _Δ
  funL2 :: ((a --> b) (_Δ |> b), (a, _Γ)) `p` (_Δ |> b)
  funL2 = funL (exR (wkR init)) (exL (wkL init))
  funR :: (a, _Γ) `p` (_Δ |> b) -> _Γ `p` (_Δ |> (a --> b) _Δ)
  funR' :: _Γ `p` (_Δ |> (a --> b) (_Δ |> b)) -> (a, _Γ) `p` (_Δ |> b)
  funR' p = cut (wkL (exR (wkR p))) funL2

  subL :: (a, _Γ) `p` (_Δ |> b) -> ((a --< b) _Δ, _Γ) `p` _Δ
  subL' :: ((a --< b) (_Δ |> b), _Γ) `p` _Δ -> (a, _Γ) `p` (_Δ |> b)
  subL' p = cut (subR (exR (wkR init)) (exL (wkL init))) (wkR (exL (wkL p)))
  subR :: _Γ `p` (_Δ |> a) -> (b, _Γ) `p` _Δ -> _Γ `p` (_Δ |> (a --< b) _Δ)

  ($$) :: _Γ `p` (_Δ |> (a --> b) (_Δ |> b)) -> _Γ `p` (_Δ |> a) -> _Γ `p` (_Δ |> b)
  f $$ a = cut (exR (wkR f)) (exR (wkR a) `funL` init)

  zeroL :: (Zero, _Γ) `p` _Δ

  oneL :: _Γ `p` _Δ -> (One, _Γ) `p` _Δ
  oneL' :: (One, _Γ) `p` _Δ -> _Γ `p` _Δ
  oneL' = cut oneR
  oneR :: _Γ `p` (_Δ |> One)

  botL :: (Bot, _Γ) `p` _Δ
  botR :: _Γ `p` _Δ -> _Γ `p` (_Δ |> Bot)
  botR' :: _Γ `p` (_Δ |> Bot) -> _Γ `p` _Δ
  botR' = (`cut` botL)

  topR :: _Γ `p` (_Δ |> Top)

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

  cut :: _Γ `p` (_Δ |> a) -> (a, _Γ) `p` _Δ -> _Γ `p` _Δ

  infixr 2 `cut`

  init :: (a, _Γ) `p` (_Δ |> a)

  wkL :: _Γ `p` _Δ -> (a, _Γ) `p` _Δ
  wkL = popL . const
  wkR :: _Γ `p` _Δ -> _Γ `p` (_Δ |> a)
  wkR = rmap Left
  cnL :: (a, (a, _Γ)) `p` _Δ -> (a, _Γ) `p` _Δ
  cnL = popL . join . pushL2
  cnR :: _Γ `p` (_Δ |> a |> a) -> _Γ `p` (_Δ |> a)
  cnR = rmap (either id pure)
  exL :: (a, (b, c)) `p` _Δ -> (b, (a, c)) `p` _Δ
  exL = popL2 . flip . pushL2
  exR :: _Γ `p` (_Δ |> a |> b) -> _Γ `p` (_Δ |> b |> a)
  exR = rmap (either (either (Left . Left) Right) (Left . Right))

  zapSum :: _Γ `p` (_Δ |> Not a _Δ & Not b _Δ) -> (a ⊕ b, _Γ) `p` _Δ
  zapSum p = sumL (cut (wkL p) (withL1 (notL init))) (cut (wkL p) (withL2 (notL init)))

  zapWith :: _Γ `p` (_Δ |> Negate a _Δ ⊕ Negate b _Δ) -> (a & b, _Γ) `p` _Δ
  zapWith p = cut (wkL p) (sumL (negateL (withL1 init)) (negateL (withL2 init)))

  zapTensor :: _Γ `p` (_Δ |> Not a _Δ ⅋ Not b _Δ) -> (a ⊗ b, _Γ) `p` _Δ
  zapTensor p = tensorL (cut (wkL (wkL p)) (parL (notL (exL (wkL init))) (notL (wkL init))))

  zapPar :: _Γ `p` (_Δ |> Negate a _Δ ⊗ Negate b _Δ) -> (a ⅋ b, _Γ) `p` _Δ
  zapPar p = cut (wkL p) (tensorL (popL2 (parL `on0` pushL (negateL init) `on1` pushL (negateL init))))


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

on0 :: (a -> b -> c) -> (a' -> a) -> (a' -> b -> c)
on0 = (.)

on1 :: (a -> b -> c) -> (b' -> b) -> (a -> b' -> c)
on1 = fmap flip . (.) . flip

infixl 4 `on0`, `on1`


newtype _Γ |- _Δ = Sequent { appSequent :: _Γ -> _Δ }
  deriving (Applicative, Category, Choice, Functor, Monad, Profunctor, Strong)

infix 2 |-


instance Proof (|-) where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  (&) = liftA2 (liftA2 inlr)

  tensorL p = popL (pushL2 p . exl <*> exr)
  (⊗) = liftA2 (liftA2 inlr)

  sumL a b = popL (exlr (pushL a) (pushL b))
  sumR1 = fmap (fmap inl)
  sumR2 = fmap (fmap inr)

  parL a b = popL (exlr (pushL a) (pushL b))
  parR ab = either (>>= (pure . inl)) (pure . inr) <$> ab

  funL a b = popL (\ f -> a `cut` popL (pure . appFun f) `cut` exL (wkL b))
  funR p = closure (\ _Γ -> pure (Fun (close _Γ . pushL p)))

  subL b = popL (\ s -> cut (pushL b (subA s)) (pushL (negateL init) (subK s)))
  subR a b = liftA2 Sub <$> a <*> negateR b

  zeroL = popL absurdP

  oneL = wkL
  oneR = pure (pure One)

  botL = popL absurdN
  botR = fmap Left

  topR = pure (pure Top)

  notL p = popL (cut p . popL . fmap pure)
  notR p = closure (\ _Γ -> pure (close _Γ . pushL p))

  negateL p = popL (cut p . popL . fmap pure)
  negateR p = closure (\ _Γ -> pure (close _Γ . pushL p))

  cut f g = f >>= either pure (pushL g)

  init = popL (pure . pure)

  popL f = Sequent (uncurry (appSequent . f))
  pushL p = Sequent . curry (appSequent p)

closure :: (_Γ -> _Δ) -> _Γ |- _Δ
closure = Sequent

close :: _Γ -> _Γ |- _Δ -> _Δ
close = flip appSequent


absurdN :: Bot -> a
absurdN = \case

absurdP :: Zero -> a
absurdP = \case
