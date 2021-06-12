{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( Proof(..)
, N
, P
) where

import Control.Applicative (liftA2)
import Control.Category (Category)
import Control.Monad (join)
import Data.Bifoldable
import Data.Bifunctor (Bifunctor(..))
import Data.Bitraversable
import Data.Functor.Identity
import Data.Profunctor
import Prelude hiding (tail)

type (<|) = (,)
infixr 5 <|
type (|>) = Either
infixl 5 |>

data a ⊗ b = !(P a) :⊗ !(P b)

infixr 7 ⊗

instance Bifoldable (⊗) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⊗) where
  bimap = bimapDefault

instance Bitraversable (⊗) where
  bitraverse f g (a :⊗ b) = fmap getP . inlr <$> traverse f a <*> traverse g b

newtype a & b = With (forall r . (N a -> N b -> r) -> r)

infixr 6 &

instance Bifoldable (&) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (&) where
  bimap = bimapDefault

instance Bitraversable (&) where
  bitraverse f g w = fmap getN . inlr <$> traverse f (exl (N w)) <*> traverse g (exr (N w))

class Conj p c | c -> p where
  inlr :: p a -> p b -> p (a `c` b)
  exl :: p (a `c` b) -> p a
  exr :: p (a `c` b) -> p b

instance Conj P (⊗) where
  inlr = fmap P . (:⊗)
  exl (P (l :⊗ _)) = l
  exr (P (_ :⊗ r)) = r

instance Conj N (&) where
  inlr a b = N $ With $ \ f -> f a b
  exl (N (With run)) = run const
  exr (N (With run)) = run (const id)

data a ⊕ b
  = InL !(P a)
  | InR !(P b)

infixr 6 ⊕

instance Bifoldable (⊕) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⊕) where
  bimap = bimapDefault

instance Bitraversable (⊕) where
  bitraverse f g = \case
    InL a -> InL <$> traverse f a
    InR b -> InR <$> traverse g b

newtype (a ⅋ b) = Par (forall r . (N a -> r) -> (N b -> r) -> r)

infixr 7 ⅋

instance Bifoldable (⅋) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⅋) where
  bimap = bimapDefault

instance Bitraversable (⅋) where
  bitraverse f g (Par run) = getN <$> run (fmap inl . traverse f) (fmap inr . traverse g)

class Disj p d | d -> p where
  inl :: p a -> p (a `d` b)
  inr :: p b -> p (a `d` b)
  exlr :: (p a -> r) -> (p b -> r) -> p (a `d` b) -> r

instance Disj P (⊕) where
  inl = P . InL
  inr = P . InR
  exlr ifl ifr = \case
    P (InL l) -> ifl l
    P (InR r) -> ifr r

instance Disj N (⅋) where
  inl l = N $ Par $ \ ifl _ -> ifl l
  inr r = N $ Par $ \ _ ifr -> ifr r
  exlr ifl ifr (N (Par run)) = run ifl ifr

newtype (a --> b) _Δ = Fun { getFun :: P a -> (_Δ |> N b) }

mkFun :: (P a -> (_Δ |> N b)) -> N ((a --> b) _Δ)
mkFun = N . Fun

appFun :: N ((a --> b) _Δ) -> (P a -> (_Δ |> N b))
appFun = getFun . getN

infixr 0 -->

data (a --< b) _Δ = Sub !(P a) !(P (Negate b _Δ))
mkSub :: P a -> P (Negate b _Δ) -> P ((a --< b) _Δ)
mkSub = fmap P . Sub

infixr 0 --<

subA :: P ((a --< b) _Δ) -> P a
subA (P (Sub a _)) = a
subK :: P ((a --< b) _Δ) -> P (Negate b _Δ)
subK (P (Sub _ k)) = k

type Not a = Cont (P a)
mkNot :: (P a -> _Δ) -> N (Not a _Δ)
mkNot = N . Cont
runNot :: N (Not a _Δ) -> P a -> _Δ
runNot = runCont . getN
type Negate a = Cont (N a)
mkNegate :: (N a -> _Δ) -> P (Negate a _Δ)
mkNegate = P . Cont
runNegate :: P (Negate a _Δ) -> N a -> _Δ
runNegate = runCont . getP

newtype Cont a _Δ = Cont { runCont :: a -> _Δ }
  deriving (Functor, Profunctor)

data Bot
data Top = Top

data Zero
data One = One

-- Polarities

newtype N a = N { getN :: a }
  deriving (Eq, Ord, Show)
  deriving (Applicative, Foldable, Functor, Monad) via Identity

instance Traversable N where
  traverse f = fmap N . f . getN

newtype P a = P { getP :: a }
  deriving (Eq, Ord, Show)
  deriving (Applicative, Foldable, Functor, Monad) via Identity

instance Traversable P where
  traverse f = fmap P . f . getP

class Profunctor p => Proof p where
  withL1 :: (N a <| _Γ) `p` _Δ -> (N (a & b) <| _Γ) `p` _Δ
  withL2 :: (N b <| _Γ) `p` _Δ -> (N (a & b) <| _Γ) `p` _Δ
  (&) :: _Γ `p` (_Δ |> N a) -> _Γ `p` (_Δ |> N b) -> _Γ `p` (_Δ |> N (a & b))
  withR1' :: _Γ `p` (_Δ |> N (a & b)) -> _Γ `p` (_Δ |> N a)
  withR1' t = cut (exR (wkR t)) (withL1 ax)
  withR2' :: _Γ `p` (_Δ |> N (a & b)) -> _Γ `p` (_Δ |> N b)
  withR2' t = cut (exR (wkR t)) (withL2 ax)

  tensorL :: (P a <| P b <| _Γ) `p` _Δ -> (P (a ⊗ b) <| _Γ) `p` _Δ
  tensorL' :: (P (a ⊗ b) <| _Γ) `p` _Δ -> (P a <| P b <| _Γ) `p` _Δ
  tensorL' = cut (exL (wkL ax) ⊗ wkL ax) . exL . wkL . exL . wkL
  (⊗) :: _Γ `p` (_Δ |> P a) -> _Γ `p` (_Δ |> P b) -> _Γ `p` (_Δ |> P (a ⊗ b))

  sumL :: (P a <| _Γ) `p` _Δ -> (P b <| _Γ) `p` _Δ -> (P (a ⊕ b) <| _Γ) `p` _Δ
  sumL1' :: (P (a ⊕ b) <| _Γ) `p` _Δ -> (P a <| _Γ) `p` _Δ
  sumL1' = cut (sumR1 ax) . exL . wkL
  sumL2' :: (P (a ⊕ b) <| _Γ) `p` _Δ -> (P b <| _Γ) `p` _Δ
  sumL2' = cut (sumR2 ax) . exL . wkL
  sumR1 :: _Γ `p` (_Δ |> P a) -> _Γ `p` (_Δ |> P (a ⊕ b))
  sumR2 :: _Γ `p` (_Δ |> P b) -> _Γ `p` (_Δ |> P (a ⊕ b))

  parL :: (N a <| _Γ) `p` _Δ -> (N b <| _Γ) `p` _Δ -> (N (a ⅋ b) <| _Γ) `p` _Δ
  parR :: _Γ `p` (_Δ |> N a |> N b) -> _Γ `p` (_Δ |> N (a ⅋ b))
  parR' :: _Γ `p` (_Δ |> N (a ⅋ b)) -> _Γ `p` (_Δ |> N a |> N b)
  parR' p = cut (exR (wkR (exR (wkR p)))) (parL (wkR ax) (exR (wkR ax)))

  funL :: _Γ `p` (_Δ |> P a) -> (N b <| _Γ) `p` _Δ -> (N ((a --> b) _Δ) <| _Γ) `p` _Δ
  funL2 :: (N ((a --> b) (_Δ |> N b)) <| P a <| _Γ) `p` (_Δ |> N b)
  funL2 = funL (exR (wkR ax)) (exL (wkL ax))
  funR :: (P a <| _Γ) `p` (_Δ |> N b) -> _Γ `p` (_Δ |> N ((a --> b) _Δ))
  funR' :: _Γ `p` (_Δ |> N ((a --> b) (_Δ |> N b))) -> (P a <| _Γ) `p` (_Δ |> N b)
  funR' p = cut (wkL (exR (wkR p))) funL2

  subL :: (P a <| _Γ) `p` (_Δ |> N b) -> (P ((a --< b) _Δ) <| _Γ) `p` _Δ
  subL' :: (P ((a --< b) (_Δ |> N b)) <| _Γ) `p` _Δ -> (P a <| _Γ) `p` (_Δ |> N b)
  subL' p = cut (subR (exR (wkR ax)) (exL (wkL ax))) (wkR (exL (wkL p)))
  subR :: _Γ `p` (_Δ |> P a) -> (N b <| _Γ) `p` _Δ -> _Γ `p` (_Δ |> P ((a --< b) _Δ))

  ($$) :: _Γ `p` (_Δ |> N ((a --> b) (_Δ |> N b))) -> _Γ `p` (_Δ |> P a) -> _Γ `p` (_Δ |> N b)
  f $$ a = cut (exR (wkR f)) (exR (wkR a) `funL` ax)

  zeroL :: (P Zero <| _Γ) `p` _Δ

  oneL :: _Γ `p` _Δ -> (P One <| _Γ) `p` _Δ
  oneL' :: (P One <| _Γ) `p` _Δ -> _Γ `p` _Δ
  oneL' = cut oneR
  oneR :: _Γ `p` (_Δ |> P One)

  botL :: (N Bot <| _Γ) `p` _Δ
  botR :: _Γ `p` _Δ -> _Γ `p` (_Δ |> N Bot)
  botR' :: _Γ `p` (_Δ |> N Bot) -> _Γ `p` _Δ
  botR' = (`cut` botL)

  topR :: _Γ `p` (_Δ |> N Top)

  negateL :: _Γ `p` (_Δ |> N a) -> (P (Negate a _Δ) <| _Γ) `p` _Δ
  negateL' :: (P (Negate a (_Δ |> N a)) <| _Γ) `p` _Δ -> _Γ `p` (_Δ |> N a)
  negateL' = cut (negateR ax) . wkR
  negateR :: (N a <| _Γ) `p` _Δ -> _Γ `p` (_Δ |> P (Negate a _Δ))
  negateR' :: _Γ `p` (_Δ |> P (Negate a _Δ)) -> (N a <| _Γ) `p` _Δ
  negateR' p = cut (wkL p) (negateL ax)

  notL :: _Γ `p` (_Δ |> P a) -> (N (Not a _Δ) <| _Γ) `p` _Δ
  notL' :: (N (Not a (_Δ |> P a)) <| _Γ) `p` _Δ -> _Γ `p` (_Δ |> P a)
  notL' = cut (notR ax) . wkR
  notR :: (P a <| _Γ) `p` _Δ -> _Γ `p` (_Δ |> N (Not a _Δ))
  notR' :: _Γ `p` (_Δ |> N (Not a _Δ)) -> (P a <| _Γ) `p` _Δ
  notR' p = cut (wkL p) (notL ax)

  cut :: _Γ `p` (_Δ |> a) -> (a <| _Γ) `p` _Δ -> _Γ `p` _Δ

  infixr `cut`

  ax :: (a, _Γ) `p` (_Δ |> a)

  wkL :: _Γ `p` _Δ -> (a <| _Γ) `p` _Δ
  wkL = popL . const
  wkR :: _Γ `p` _Δ -> _Γ `p` (_Δ |> a)
  wkR = rmap Left
  cnL :: (a <| a <| _Γ) `p` _Δ -> (a <| _Γ) `p` _Δ
  cnL = popL . join . pushL2
  cnR :: _Γ `p` (_Δ |> a |> a) -> _Γ `p` (_Δ |> a)
  cnR = rmap (either id pure)
  exL :: (a <| b <| c) `p` _Δ -> (b <| a <| c) `p` _Δ
  exL = popL2 . flip . pushL2
  exR :: _Γ `p` (a |> b |> c) -> _Γ `p` (a |> c |> b)
  exR = rmap (either (either (Left . Left) Right) (Left . Right))

  zapSum :: _Γ `p` (_Δ |> N (Not a _Δ & Not b _Δ)) -> (P (a ⊕ b) <| _Γ) `p` _Δ
  zapSum p = sumL (cut (wkL p) (withL1 (notL ax))) (cut (wkL p) (withL2 (notL ax)))

  zapWith :: _Γ `p` (_Δ |> P (Negate a _Δ ⊕ Negate b _Δ)) -> (N (a & b) <| _Γ) `p` _Δ
  zapWith p = cut (wkL p) (sumL (negateL (withL1 ax)) (negateL (withL2 ax)))

  zapTensor :: _Γ `p` (_Δ |> N (Not a _Δ ⅋ Not b _Δ)) -> (P (a ⊗ b) <| _Γ) `p` _Δ
  zapTensor p = tensorL (cut (wkL (wkL p)) (parL (notL (exL (wkL ax))) (notL (wkL ax))))

  zapPar :: _Γ `p` (_Δ |> P (Negate a _Δ ⊗ Negate b _Δ)) -> (N (a ⅋ b) <| _Γ) `p` _Δ
  zapPar p = cut (wkL p) (tensorL (popL2 (parL `on0` pushL (negateL ax) `on1` pushL (negateL ax))))


  -- | Pop something off the context which can later be pushed. Used with 'pushL', this provides a generalized context reordering facility.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  popL :: (a -> _Γ `p` _Δ) -> (a <| _Γ) `p` _Δ

  -- | Push something onto the context which was previously popped off it. Used with 'popL', this provides a generalized context reordering facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL :: (a <| _Γ) `p` _Δ -> a -> _Γ `p` _Δ

  popL2 :: (a -> b -> _Γ `p` _Δ) -> (a <| b <| _Γ) `p` _Δ
  popL2 f = popL (popL . f)

  pushL2 :: (a <| b <| _Γ) `p` _Δ -> a -> b -> _Γ `p` _Δ
  pushL2 p = pushL . pushL p

on0 ::  (a -> b -> c) -> (a' -> a) -> (a' -> b -> c)
on0 = (.)

on1 :: (a -> b -> c) -> (b' -> b) -> (a -> b' -> c)
on1 = fmap flip . (.) . flip

infixl 4 `on0`, `on1`


newtype _Γ |- _Δ = Sequent { appSequent :: _Γ -> _Δ }
  deriving (Applicative, Category, Functor, Monad, Profunctor, Strong)

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
  funR p = closure (\ _Γ -> pure (mkFun (close _Γ . pushL p)))

  subL b = popL (\ s -> cut (pushL b (subA s)) (pushL (negateL ax) (subK s)))
  subR a b = liftA2 mkSub <$> a <*> negateR b

  zeroL = popL (absurdP . getP)

  oneL = wkL
  oneR = pure (pure (P One))

  botL = popL (absurdN . getN)
  botR = fmap Left

  topR = pure (pure (N Top))

  notL p = popL (cut p . popL . fmap pure . runNot)
  notR p = closure (\ _Γ -> pure (mkNot (close _Γ . pushL p)))

  negateL p = popL (cut p . popL . fmap pure . runNegate)
  negateR p = closure (\ _Γ -> pure (mkNegate (close _Γ . pushL p)))

  cut f g = f >>= either pure (pushL g)

  ax = popL (pure . pure)

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
