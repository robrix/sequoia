{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( Core(..)
, Structural(..)
, Negative(..)
, Additive(..)
, Multiplicative(..)
, Implicative(..)
, N(..)
, P(..)
, Γ(..)
, Δ
) where

import Control.Applicative (liftA2)
import Control.Monad (ap, join)
import Data.Bifoldable
import Data.Bifunctor (Bifunctor(..))
import Data.Bitraversable
import Prelude hiding (init, tail)

type (*) = (,)
infixr 4 *

type (+) = Either
infixl 4 +

split :: (os + a -> r) -> (os -> r, a -> r)
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

newtype a ⅋ b = Par (forall r . (a -> r) -> (b -> r) -> r)

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


newtype N a = N { getN :: a }
newtype P a = P { getP :: a }


data Γ = Γ
data Δ


class Core p where
  (>>>) :: is `p` (os + a) -> (a * is) `p` os -> is `p` os

  init :: (a * is) `p` (os + a)


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
  popL :: (a -> is `p` os) -> (a * is) `p` os

  -- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL :: (a * is) `p` os -> a -> is `p` os

  popL2 :: (a -> b -> is `p` os) -> (a * b * is) `p` os
  popL2 f = popL (popL . f)

  pushL2 :: (a * b * is) `p` os -> a -> b -> is `p` os
  pushL2 p = pushL . pushL p


  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR :: ((a -> Δ) -> is `p` os) -> is `p` (os + a)

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR :: is `p` (os + a) -> ((a -> Δ) -> is `p` os)

  popR2 :: ((a -> Δ) -> (b -> Δ) -> is `p` os) -> is `p` (os + b + a)
  popR2 f = popR (popR . f)

  pushR2 :: is `p` (os + b + a) -> (a -> Δ) -> (b -> Δ) -> is `p` os
  pushR2 p = pushR . pushR p


  wkL :: is `p` os -> (a * is) `p` os
  wkL = popL . const
  wkR :: is `p` os -> is `p` (os + a)
  wkR = popR . const
  cnL :: (a * a * is) `p` os -> (a * is) `p` os
  cnL = popL . join . pushL2
  cnR :: is `p` (os + a + a) -> is `p` (os + a)
  cnR = popR . join . pushR2
  exL :: (a * b * c) `p` os -> (b * a * c) `p` os
  exL = popL2 . flip . pushL2
  exR :: is `p` (os + a + b) -> is `p` (os + b + a)
  exR = popR2 . flip . pushR2


class (Core p, Structural p) => Negative p where
  negateL :: is `p` (os + a) -> (Negate a * is) `p` os
  negateL' :: (Negate a * is) `p` os -> is `p` (os + a)
  negateL' p = negateR init >>> wkR p
  negateR :: (a * is) `p` os -> is `p` (os + Negate a)
  negateR' :: is `p` (os + Negate a) -> (a * is) `p` os
  negateR' p = wkL p >>> negateL init

  notL :: is `p` (os + a) -> (Not a * is) `p` os
  notL' :: (Not a * is) `p` os -> is `p` (os + a)
  notL' p = notR init >>> wkR p
  notR :: (a * is) `p` os -> is `p` (os + Not a)
  notR' :: is `p` (os + Not a) -> (a * is) `p` os
  notR' p = wkL p >>> notL init


class (Core p, Structural p, Negative p) => Additive p where
  zeroL :: (Zero * is) `p` os

  topR :: is `p` (os + Top)

  sumL :: (a * is) `p` os -> (b * is) `p` os -> (a ⊕ b * is) `p` os
  sumL p1 p2 = sumLWith (notR p1 & notR p2)
  sumL1' :: (a ⊕ b * is) `p` os -> (a * is) `p` os
  sumL1' p = sumR1 init >>> exL (wkL p)
  sumL2' :: (a ⊕ b * is) `p` os -> (b * is) `p` os
  sumL2' p = sumR2 init >>> exL (wkL p)
  sumLWith :: is `p` (os + Not a & Not b) -> (a ⊕ b * is) `p` os
  sumLWith p = wkL p >>> exL (sumL (exL (withL1 (notL init))) (exL (withL2 (notL init))))
  sumR1 :: is `p` (os + a) -> is `p` (os + a ⊕ b)
  sumR2 :: is `p` (os + b) -> is `p` (os + a ⊕ b)

  withL1 :: (a * is) `p` os -> (a & b * is) `p` os
  withL1 = withLSum . sumR1 . negateR
  withL2 :: (b * is) `p` os -> (a & b * is) `p` os
  withL2 = withLSum . sumR2 . negateR
  withLSum :: is `p` (os + Negate a ⊕ Negate b) -> (a & b * is) `p` os
  withLSum p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
  (&) :: is `p` (os + a) -> is `p` (os + b) -> is `p` (os + a & b)
  withR1' :: is `p` (os + a & b) -> is `p` (os + a)
  withR1' t = exR (wkR t) >>> withL1 init
  withR2' :: is `p` (os + a & b) -> is `p` (os + b)
  withR2' t = exR (wkR t) >>> withL2 init

  zapSum :: is `p` (os + Not a & Not b) -> (a ⊕ b * is) `p` os
  zapSum p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))

  zapWith :: is `p` (os + Negate a ⊕ Negate b) -> (a & b * is) `p` os
  zapWith p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))


class (Core p, Structural p, Negative p) => Multiplicative p where
  botL :: (Bot * is) `p` os
  botR :: is `p` os -> is `p` (os + Bot)
  botR' :: is `p` (os + Bot) -> is `p` os
  botR' = (>>> botL)

  oneL :: is `p` os -> (One * is) `p` os
  oneL' :: (One * is) `p` os -> is `p` os
  oneL' = (oneR >>>)
  oneR :: is `p` (os + One)

  parL :: (a * is) `p` os -> (b * is) `p` os -> (a ⅋ b * is) `p` os
  parL p1 p2 = parLTensor (negateR p1 ⊗ negateR p2)
  parLTensor :: is `p` (os + Negate a ⊗ Negate b) -> (a ⅋ b * is) `p` os
  parLTensor p = wkL p >>> tensorL (negateL (negateL (parL (wkR init) init)))
  parR :: is `p` (os + a + b) -> is `p` (os + a ⅋ b)
  parR' :: is `p` (os + a ⅋ b) -> is `p` (os + a + b)
  parR' p = exR (wkR (exR (wkR p))) >>> parL (wkR init) init

  tensorL :: (a * b * is) `p` os -> (a ⊗ b * is) `p` os
  tensorL = tensorLPar . parR . notR . notR
  tensorLPar :: is `p` (os + Not a ⅋ Not b) -> (a ⊗ b * is) `p` os
  tensorLPar p = wkL p >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
  tensorL' :: (a ⊗ b * is) `p` os -> (a * b * is) `p` os
  tensorL' p = init ⊗ wkL init >>> popL (wkL . wkL . pushL p)
  (⊗) :: is `p` (os + a) -> is `p` (os + b) -> is `p` (os + a ⊗ b)

  zapTensor :: is `p` (os + Not a ⅋ Not b) -> (a ⊗ b * is) `p` os
  zapTensor p = tensorL (wkL (wkL p) >>> parL (notL init) (notL (wkL init)))

  zapPar :: is `p` (os + Negate a ⊗ Negate b) -> (a ⅋ b * is) `p` os
  zapPar p = wkL p >>> tensorL (popL2 (parL `on0` pushL (negateL init) `on1` pushL (negateL init)))


class (Core p, Structural p, Negative p) => Implicative p where
  funL :: is `p` (os + a) -> (b * is) `p` os -> (a --> b * is) `p` os
  funL pa pb = funLSub (subR pa pb)
  funLSub :: is `p` (os + a --< b) -> (a --> b * is) `p` os
  funLSub p = wkL p >>> subL (exL (funL init init))
  funL2 :: (a --> b * a * is) `p` (os + b)
  funL2 = funL init init
  funR :: (a * is) `p` (os + b) -> is `p` (os + a --> b)
  funR' :: is `p` (os + a --> b) -> (a * is) `p` (os + b)
  funR' p = wkL (exR (wkR p)) >>> funL2

  subL :: (a * is) `p` (os + b) -> (a --< b * is) `p` os
  subL = subLFun . funR
  subLFun :: is `p` (os + a --> b) -> (a --< b * is) `p` os
  subLFun p = wkL p >>> exL (subL (exL (funL init init)))
  subL' :: (a --< b * is) `p` os -> (a * is) `p` (os + b)
  subL' p = subR init init >>> wkR (exL (wkL p))
  subR :: is `p` (os + a) -> (b * is) `p` os -> is `p` (os + a --< b)

  ($$) :: is `p` (os + a --> b) -> is `p` (os + a) -> is `p` (os + b)
  f $$ a = exR (wkR f) >>> exR (wkR a) `funL` init

on0 :: (a -> b -> c) -> (a' -> a) -> (a' -> b -> c)
on0 = (.)

on1 :: (a -> b -> c) -> (b' -> b) -> (a -> b' -> c)
on1 = fmap flip . (.) . flip

infixl 4 `on0`, `on1`


newtype is |- os = Seq ((os -> Δ) -> (is -> Δ))
  deriving (Functor)

infix 2 |-

appSeq :: (os -> Δ) -> is -> is |- os -> Δ
appSeq k c (Seq run) = run k c

instance Applicative ((|-) is) where
  pure a = Seq $ \ k _ -> k a
  (<*>) = ap

instance Monad ((|-) is) where
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
  funL a b = popL (\ f -> a >>> Seq (\ k (a, is) -> appFun f (appSeq k is . pushL b) a))
  funR (Seq run) = Seq $ \ k c -> let (k', ka) = split k in ka (Fun (\ kb -> run (either k' kb) . (,c)))

  subL b = popL (\ s -> pushL b (subA s) >>> pushL (negateL init) (subK s))
  subR a b = liftA2 Sub <$> a <*> negateR b


absurdN :: Bot -> a
absurdN = \case

absurdP :: Zero -> a
absurdP = \case
