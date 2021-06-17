{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( -- * Sequents
  runSeq
, runSeqIO
, Seq(..)
  -- * Contexts
, type (<|)
, type (|>)
, Γ(..)
, Δ
  -- * Polarity
, N(..)
, P(..)
  -- * Core rules
, Core(..)
, Structural(..)
  -- * Negating
, Not(..)
, runNot
, not'
, Negate(..)
, runNegate
, negate'
, Negative(..)
  -- * Additive
, Top(..)
, Zero
, type (&)(..)
, type (⊕)(..)
, Additive(..)
  -- * Multiplicative
, Bot
, One(..)
, type (⅋)(..)
, type (⊗)(..)
, Multiplicative(..)
  -- * Implicative
, type (-->)(..)
, appFun
, fun
, type (--<)(..)
, sub
, Implicative(..)
) where

import Control.Applicative (liftA2)
import Control.Exception (Exception, catch, throw)
import Control.Monad (ap, join)
import Data.Bifoldable
import Data.Bifunctor (Bifunctor(..))
import Data.Bitraversable
import Data.Functor.Identity
import Data.Traversable (foldMapDefault)
import Prelude hiding (init)

-- Sequents

runSeq :: (os -> Δ) -> is -> Seq is os -> Δ
runSeq k c (Seq run) = run k c

runSeqIO :: (os -> IO ()) -> is -> Seq is os -> IO ()
runSeqIO k is (Seq run) = absurdΔ (run (throw . Escape . k) is) `catch` getEscape

newtype Escape = Escape { getEscape :: IO () }

instance Show Escape where show _ = "Escape"
instance Exception Escape


newtype Seq is os = Seq ((os -> Δ) -> (is -> Δ))
  deriving (Functor)

instance Applicative (Seq is) where
  pure a = Seq $ \ k _ -> k a
  (<*>) = ap

instance Monad (Seq is) where
  Seq a >>= f = Seq $ \ k c -> a (runSeq k c . f) c


-- Contexts

type (<|) = (,)
infixr 4 <|

type (|>) = Either
infixl 4 |>

split :: (os |> a -> r) -> (os -> r, a -> r)
split f = (f . Left, f . Right)


data Γ = Γ
  deriving (Eq, Ord, Show)


data Δ

absurdΔ :: Δ -> a
absurdΔ = \case


-- Polarity

class (Functor f, Functor u) => Adjunction f u | f -> u, u -> f where
  {-# MINIMAL (unit | leftAdjunct), (counit | rightAdjunct) #-}
  unit :: a -> u (f a)
  unit = leftAdjunct id
  counit :: f (u a) -> a
  counit = rightAdjunct id

  leftAdjunct :: (f a -> b) -> (a -> u b)
  leftAdjunct f = fmap f . unit
  rightAdjunct :: (a -> u b) -> (f a -> b)
  rightAdjunct f = counit . fmap f


newtype N a = N { getN :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Adjunction N P where
  unit   =    P .    N
  counit = getP . getN
  leftAdjunct  f =    P . f .    N
  rightAdjunct f = getP . f . getN


newtype P a = P { getP :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Adjunction P N where
  unit   =    N .    P
  counit = getN . getP
  leftAdjunct  f =    N . f .    P
  rightAdjunct f = getN . f . getP


-- Core rules

class Core p where
  (>>>) :: is `p` (os |> a) -> (a <| is) `p` os -> is `p` os

  init :: (a <| is) `p` (os |> a)

infixr 1 >>>

instance Core Seq where
  f >>> g = f >>= either pure (pushL g)

  init = popL (pure . pure)


class Structural p where
  -- | Pop something off the input context which can later be pushed. Used with 'pushL', this provides a generalized context restructuring facility.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  popL :: (a -> is `p` os) -> (a <| is) `p` os

  poppedL :: (is `p` os -> is' `p` os) -> ((a <| is) `p` os -> (a <| is') `p` os)
  poppedL f p = popL (f . pushL p)

  -- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL :: (a <| is) `p` os -> a -> is `p` os

  popL2 :: (a -> b -> is `p` os) -> (a <| b <| is) `p` os
  popL2 f = popL (popL . f)

  pushL2 :: (a <| b <| is) `p` os -> a -> b -> is `p` os
  pushL2 p = pushL . pushL p


  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR :: ((a -> Δ) -> is `p` os) -> is `p` (os |> a)

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR :: is `p` (os |> a) -> ((a -> Δ) -> is `p` os)

  popR2 :: ((a -> Δ) -> (b -> Δ) -> is `p` os) -> is `p` (os |> b |> a)
  popR2 f = popR (popR . f)

  pushR2 :: is `p` (os |> b |> a) -> (a -> Δ) -> (b -> Δ) -> is `p` os
  pushR2 p = pushR . pushR p


  instantiateL :: Γ `p` os -> is `p` os
  instantiateR :: is `p` Δ -> is `p` os
  instantiate :: Γ `p` Δ -> is `p` os
  instantiate = instantiateL . instantiateR

  abstractL :: is -> is `p` os -> Γ `p` os
  abstractR :: (os -> os') -> is `p` os -> is `p` os'
  abstract :: is -> (os -> os') -> is `p` os -> Γ `p` os'
  abstract i k = abstractL i . abstractR k


  wkL :: is `p` os -> (a <| is) `p` os
  wkL = popL . const
  wkR :: is `p` os -> is `p` (os |> a)
  wkR = popR . const
  cnL :: (a <| a <| is) `p` os -> (a <| is) `p` os
  cnL = popL . join . pushL2
  cnR :: is `p` (os |> a |> a) -> is `p` (os |> a)
  cnR = popR . join . pushR2
  exL :: (a <| b <| c) `p` os -> (b <| a <| c) `p` os
  exL = popL2 . flip . pushL2
  exR :: is `p` (os |> a |> b) -> is `p` (os |> b |> a)
  exR = popR2 . flip . pushR2

instance Structural Seq where
  popL f = Seq $ \ k -> uncurry (flip (runSeq k) . f)
  pushL (Seq run) a = Seq $ \ k -> run k . (a,)

  popR f = Seq $ \ k c -> let (k', ka) = split k in runSeq k' c (f ka)
  pushR (Seq run) a = Seq $ \ k -> run (either k a)

  instantiateL (Seq run) = Seq (\ k -> run k . const Γ)
  instantiateR = fmap absurdΔ

  abstractL i (Seq run) = Seq (\ k Γ -> run k i)
  abstractR = fmap


-- Negating

newtype Not    a = Not    { getNot    :: Seq (P a <| Γ) Δ }

runNot :: N (Not a) -> Seq (P a <| Γ) Δ
runNot = getNot . getN

not' :: Seq (P a <| Γ) Δ -> N (Not a)
not' = N . Not


newtype Negate a = Negate { getNegate :: Seq (N a <| Γ) Δ }

runNegate :: P (Negate a) -> Seq (N a <| Γ) Δ
runNegate = getNegate . getP

negate' :: Seq (N a <| Γ) Δ -> P (Negate a)
negate' = P . Negate


class (Core p, Structural p) => Negative p where
  notL :: is `p` (os |> P a) -> (N (Not a) <| is) `p` os
  notL' :: (N (Not a) <| is) `p` os -> is `p` (os |> P a)
  notL' p = notR init >>> wkR p
  notR :: (P a <| is) `p` os -> is `p` (os |> N (Not a))
  notR' :: is `p` (os |> N (Not a)) -> (P a <| is) `p` os
  notR' p = wkL p >>> notL init

  negateL :: is `p` (os |> N a) -> (P (Negate a) <| is) `p` os
  negateL' :: (P (Negate a) <| is) `p` os -> is `p` (os |> N a)
  negateL' p = negateR init >>> wkR p
  negateR :: (N a <| is) `p` os -> is `p` (os |> P (Negate a))
  negateR' :: is `p` (os |> P (Negate a)) -> (N a <| is) `p` os
  negateR' p = wkL p >>> negateL init

instance Negative Seq where
  negateL p = popL (\ negateA -> p >>> popL (instantiate . pushL (runNegate negateA)))
  negateR (Seq run) = Seq $ \ k c -> let (k', ka) = split k in ka (negate' (Seq (const (run k' . (c <$)))))

  notL p = popL (\ notA -> p >>> popL (instantiate . pushL (runNot notA)))
  notR (Seq run) = Seq $ \ k c -> let (k', ka) = split k in ka (not' (Seq (const (run k' . (c <$)))))


-- Additive

data Top = Top
  deriving (Eq, Ord, Show)


data Zero

absurdP :: P Zero -> a
absurdP = \case


newtype a & b = With (forall r . (a -> b -> r) -> r)
  deriving (Functor)

infixr 6 &

instance Foldable ((&) a) where
  foldMap = foldMapDefault

instance Traversable ((&) a) where
  traverse f (With run) = run $ \ a b -> let mk b = With (\ f -> f a b) in mk <$> f b

instance Bifoldable (&) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (&) where
  bimap = bimapDefault

instance Bitraversable (&) where
  bitraverse f g w = inlr <$> f (exl w) <*> g (exr w)

instance Conj (&) where
  inlr a b = With $ \ f -> f a b
  exl (With run) = run const
  exr (With run) = run (const id)


data a ⊕ b
  = InL !a
  | InR !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 ⊕

instance Bifoldable (⊕) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⊕) where
  bimap = bimapDefault

instance Bitraversable (⊕) where
  bitraverse f g = \case
    InL a -> InL <$> f a
    InR b -> InR <$> g b

instance Disj (⊕) where
  inl = InL
  inr = InR
  exlr ifl ifr = \case
    InL l -> ifl l
    InR r -> ifr r


class (Core p, Structural p, Negative p) => Additive p where
  zeroL :: (P Zero <| is) `p` os

  topR :: is `p` (os |> N Top)

  sumL :: (P a <| is) `p` os -> (P b <| is) `p` os -> (P (a ⊕ b) <| is) `p` os
  sumL p1 p2 = sumLWith (notR p1 & notR p2)
  sumL1' :: (P (a ⊕ b) <| is) `p` os -> (P a <| is) `p` os
  sumL1' p = sumR1 init >>> exL (wkL p)
  sumL2' :: (P (a ⊕ b) <| is) `p` os -> (P b <| is) `p` os
  sumL2' p = sumR2 init >>> exL (wkL p)
  sumLWith :: is `p` (os |> N (Not a & Not b)) -> (P (a ⊕ b) <| is) `p` os
  sumLWith p = wkL p >>> exL (sumL (exL (withL1 (notL init))) (exL (withL2 (notL init))))
  sumR1 :: is `p` (os |> P a) -> is `p` (os |> P (a ⊕ b))
  sumR2 :: is `p` (os |> P b) -> is `p` (os |> P (a ⊕ b))

  withL1 :: (N a <| is) `p` os -> (N (a & b) <| is) `p` os
  withL1 = withLSum . sumR1 . negateR
  withL2 :: (N b <| is) `p` os -> (N (a & b) <| is) `p` os
  withL2 = withLSum . sumR2 . negateR
  withLSum :: is `p` (os |> P (Negate a ⊕ Negate b)) -> (N (a & b) <| is) `p` os
  withLSum p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
  (&) :: is `p` (os |> N a) -> is `p` (os |> N b) -> is `p` (os |> N (a & b))
  withR1' :: is `p` (os |> N (a & b)) -> is `p` (os |> N a)
  withR1' t = exR (wkR t) >>> withL1 init
  withR2' :: is `p` (os |> N (a & b)) -> is `p` (os |> N b)
  withR2' t = exR (wkR t) >>> withL2 init

  zapSum :: is `p` (os |> N (Not a & Not b)) -> (P (a ⊕ b) <| is) `p` os
  zapSum p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))

  zapWith :: is `p` (os |> P (Negate a ⊕ Negate b)) -> (N (a & b) <| is) `p` os
  zapWith p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))

instance Additive Seq where
  zeroL = popL absurdP

  topR = pure (pure (N Top))

  sumL a b = popL (exlrP (pushL a) (pushL b))
  sumR1 = fmap (fmap inlP)
  sumR2 = fmap (fmap inrP)

  withL1 p = popL (pushL p . exlP)
  withL2 p = popL (pushL p . exrP)
  (&) = liftA2 (liftA2 inlrP)


-- Multiplicative

data Bot

absurdN :: N Bot -> a
absurdN = \case


data One = One
  deriving (Eq, Ord, Show)


newtype a ⅋ b = Par (forall r . (a -> r) -> (b -> r) -> r)
  deriving (Functor)

infixr 7 ⅋

instance Foldable ((⅋) a) where
  foldMap = foldMapDefault

instance Traversable ((⅋) a) where
  traverse f (Par run) = run (pure . inl) (fmap inr . f)

instance Bifoldable (⅋) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⅋) where
  bimap = bimapDefault

instance Bitraversable (⅋) where
  bitraverse f g (Par run) = run (fmap inl . f) (fmap inr . g)

instance Disj (⅋) where
  inl l = Par $ \ ifl _ -> ifl l
  inr r = Par $ \ _ ifr -> ifr r
  exlr ifl ifr (Par run) = run ifl ifr


data a ⊗ b = !a :⊗ !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ⊗

instance Bifoldable (⊗) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⊗) where
  bimap = bimapDefault

instance Bitraversable (⊗) where
  bitraverse f g (a :⊗ b) = (:⊗) <$> f a <*> g b

instance Conj (⊗) where
  inlr = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r


class (Core p, Structural p, Negative p) => Multiplicative p where
  botL :: (N Bot <| is) `p` os
  botR :: is `p` os -> is `p` (os |> N Bot)
  botR' :: is `p` (os |> N Bot) -> is `p` os
  botR' = (>>> botL)

  oneL :: is `p` os -> (P One <| is) `p` os
  oneL' :: (P One <| is) `p` os -> is `p` os
  oneL' = (oneR >>>)
  oneR :: is `p` (os |> P One)

  parL :: (N a <| is) `p` os -> (N b <| is) `p` os -> (N (a ⅋ b) <| is) `p` os
  parL p1 p2 = parLTensor (negateR p1 ⊗ negateR p2)
  parLTensor :: is `p` (os |> P (Negate a ⊗ Negate b)) -> (N (a ⅋ b) <| is) `p` os
  parLTensor p = wkL p >>> tensorL (negateL (negateL (parL (wkR init) init)))
  parR :: is `p` (os |> N a |> N b) -> is `p` (os |> N (a ⅋ b))
  parR' :: is `p` (os |> N (a ⅋ b)) -> is `p` (os |> N a |> N b)
  parR' p = exR (wkR (exR (wkR p))) >>> parL (wkR init) init

  tensorL :: (P a <| P b <| is) `p` os -> (P (a ⊗ b) <| is) `p` os
  tensorL = tensorLPar . parR . notR . notR
  tensorLPar :: is `p` (os |> N (Not a ⅋ Not b)) -> (P (a ⊗ b) <| is) `p` os
  tensorLPar p = wkL p >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
  tensorL' :: (P (a ⊗ b) <| is) `p` os -> (P a <| P b <| is) `p` os
  tensorL' p = init ⊗ wkL init >>> popL (wkL . wkL . pushL p)
  (⊗) :: is `p` (os |> P a) -> is `p` (os |> P b) -> is `p` (os |> P (a ⊗ b))

  zapTensor :: is `p` (os |> N (Not a ⅋ Not b)) -> (P (a ⊗ b) <| is) `p` os
  zapTensor p = tensorL (wkL (wkL p) >>> parL (notL init) (notL (wkL init)))

  zapPar :: is `p` (os |> P (Negate a ⊗ Negate b)) -> (N (a ⅋ b) <| is) `p` os
  zapPar p = wkL p >>> tensorL (popL2 (parL `on0` pushL (negateL init) `on1` pushL (negateL init)))


instance Multiplicative Seq where
  botL = popL absurdN
  botR = fmap Left

  oneL = wkL
  oneR = pure (pure (P One))

  parL a b = popL (exlrP (pushL a) (pushL b))
  parR ab = either (>>= (pure . inlP)) (pure . inrP) <$> ab

  tensorL p = popL (pushL2 p . exlP <*> exrP)
  (⊗) = liftA2 (liftA2 inlrP)


-- Implicative

newtype a --> b = Fun { getFun :: P (Negate b) -> N (Not a) }

infixr 5 -->

appFun :: N (a --> b) -> (P (Negate b) -> N (Not a))
appFun = getFun . getN

fun :: (P (Negate b) -> N (Not a)) -> N (a --> b)
fun = N . Fun


data a --< b = Sub { subA :: !(P a), subK :: !(P (Negate b)) }

infixr 5 --<

sub :: P a -> P (Negate b) -> P (a --< b)
sub = fmap P . Sub


class (Core p, Structural p, Negative p) => Implicative p where
  funL :: is `p` (os |> P a) -> (N b <| is) `p` os -> (N (a --> b) <| is) `p` os
  funL pa pb = funLSub (subR pa pb)
  funLSub :: is `p` (os |> P (a --< b)) -> (N (a --> b) <| is) `p` os
  funLSub p = wkL p >>> subL (exL (funL init init))
  funL2 :: (N (a --> b) <| P a <| is) `p` (os |> N b)
  funL2 = funL init init
  funR :: (P a <| is) `p` (os |> N b) -> is `p` (os |> N (a --> b))
  funR' :: is `p` (os |> N (a --> b)) -> (P a <| is) `p` (os |> N b)
  funR' p = wkL (exR (wkR p)) >>> funL2

  subL :: (P a <| is) `p` (os |> N b) -> (P (a --< b) <| is) `p` os
  subL = subLFun . funR
  subLFun :: is `p` (os |> N (a --> b)) -> (P (a --< b) <| is) `p` os
  subLFun p = wkL p >>> exL (subL (exL (funL init init)))
  subL' :: (P (a --< b) <| is) `p` os -> (P a <| is) `p` (os |> N b)
  subL' p = subR init init >>> wkR (exL (wkL p))
  subR :: is `p` (os |> P a) -> (N b <| is) `p` os -> is `p` (os |> P (a --< b))

  ($$) :: is `p` (os |> N (a --> b)) -> is `p` (os |> P a) -> is `p` (os |> N b)
  f $$ a = exR (wkR f) >>> exR (wkR a) `funL` init


instance Implicative Seq where
  funL a b = popL (\ f -> a >>> Seq (\ k (a, is) -> runSeq id (a, Γ) (runNot (appFun f (negate' (popL (abstract is k . pushL b)))))))
  funR (Seq run) = Seq $ \ k c -> let (k', ka) = split k in ka (fun (\ kb -> not' (Seq (const (run (either k' (\ a -> runSeq id (a, Γ) (runNegate kb))) . (c <$))))))

  subL b = popL (\ (P s) -> pushL b (subA s) >>> pushL (negateL init) (subK s))
  subR a b = liftA2 sub <$> a <*> negateR b


-- Utilities

on0 :: (a -> b -> c) -> (a' -> a) -> (a' -> b -> c)
on0 = (.)

on1 :: (a -> b -> c) -> (b' -> b) -> (a -> b' -> c)
on1 = fmap flip . (.) . flip

infixl 4 `on0`, `on1`


class Conj c where
  inlr :: a -> b -> a `c` b
  exl :: (a `c` b) -> a
  exr :: (a `c` b) -> b

instance Conj (,) where
  inlr = (,)
  exl = fst
  exr = snd

inlrP :: (Conj c, Applicative p) => p a -> p b -> p (a `c` b)
inlrP = liftA2 inlr

exlP :: (Conj c, Functor p) => p (a `c` b) -> p a
exlP = fmap exl

exrP :: (Conj c, Functor p) => p (a `c` b) -> p b
exrP = fmap exr


class Disj d where
  inl :: a -> a `d` b
  inr :: b -> a `d` b
  exlr :: (a -> r) -> (b -> r) -> ((a `d` b) -> r)

instance Disj Either where
  inl = Left
  inr = Right
  exlr = either

inlP :: (Disj d, Functor p) => p a -> p (a `d` b)
inlP = fmap inl

inrP :: (Disj d, Functor p) => p b -> p (a `d` b)
inrP = fmap inr

exlrP :: (Adjunction p p', Disj d) => (p a -> r) -> (p b -> r) -> (p (a `d` b) -> r)
exlrP f g = rightAdjunct (exlr (leftAdjunct f) (leftAdjunct g))
