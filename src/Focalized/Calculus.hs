{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( -- * Sequents
  runSeq
, Seq(..)
, liftL
, liftR
, liftLR
, lowerL
, lowerR
, lowerLR
  -- * Effectful sequents
, runSeqT
, SeqT(..)
  -- * Contexts
, type (<|)
, (<|)
, type (|>)
, (|>)
, Γ(..)
, Δ
  -- * Core rules
, Core(..)
, Structural(..)
  -- * Negating
, Not(..)
, Negate(..)
, Negative(..)
  -- * Additive
, Top(..)
, Zero
, type (&)(..)
, type (⊕)
, Additive(..)
  -- * Multiplicative
, Bot
, One(..)
, type (⅋)
, type (⊗)(..)
, Multiplicative(..)
  -- * Implicative
, Fun(..)
, type (-->)
, Sub(..)
, type (--<)
, Implicative(..)
  -- * Quantifying
, ForAll(..)
, Exists(..)
, Quantifying(..)
  -- * Recursive
, Nu(..)
, NuF(..)
, Mu(..)
, MuF(..)
, Recursive(..)
  -- * Polarity
, N(..)
, P(..)
, Polarized(..)
, Neg
, Pos
, Up(..)
, Down(..)
, Shifting(..)
  -- * Utilities
, mapK
, runK
, K(..)
, cps
, liftCPS
, runCPS
, CPS(..)
, Conj(..)
, curryConj
, uncurryConj
, Disj(..)
) where

import           Control.Applicative (liftA2)
import qualified Control.Category as Cat
import           Control.Monad (ap, join)
import           Control.Monad.Trans.Class
import           Data.Functor.Identity
import           Data.Kind (Constraint)
import           Prelude hiding (init)

-- Sequents

runSeq :: (o -> r) -> i -> Seq r i o -> r
runSeq k c = runCPS k c . getSeq

sequent :: ((o -> r) -> (i -> r)) -> Seq r i o
sequent = Seq . cps

newtype Seq r i o = Seq { getSeq :: CPS r i o }
  deriving (Applicative, Functor, Monad)

liftL :: (a -> r) -> Seq r (a <| i) o
liftL ka = sequent $ \ _ -> ka . exl

liftR :: a -> Seq r i (o |> a)
liftR = pure . inr

liftLR :: (a -> b) -> Seq r (a <| i) (o |> b)
liftLR f = sequent $ \ k -> k . inr . f . exl

lowerL :: ((a -> r) -> Seq r i o) -> Seq r (a <| i) o -> Seq r i o
lowerL f p = sequent $ \ k c -> runSeq k c (f (\ a -> runSeq k (a <| c) p))

lowerR :: (Core p, Structural p) => (a -> p r i o) -> p r i (o |> a) -> p r i o
lowerR k p = p >>> popL k

lowerLR :: (((b -> r) -> (a -> r)) -> Seq r i o) -> Seq r (a <| i) (o |> b) -> Seq r i o
lowerLR f p = sequent $ \ k c -> runSeq k c (f (\ kb a -> runSeq (k |> kb) (a <| c) p))


-- Effectful sequents

runSeqT :: (o -> m r) -> i -> SeqT r i m o -> m r
runSeqT k i = runSeq k i . getSeqT

newtype SeqT r i m o = SeqT { getSeqT :: Seq (m r) i o }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r i) where
  lift m = SeqT (Seq (cps (\ k _ -> m >>= k)))


-- Contexts

data a <| b = a :<| b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 4 <|

instance Conj (<|) where
  inlr = (:<|)
  exl (a :<| _) = a
  exr (_ :<| b) = b

(<|) :: i -> is -> i <| is
(<|) = inlr

data a |> b
  = L a
  | R b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 4 |>

instance Disj (|>) where
  inl = L
  inr = R
  exlr f g = \case
    L a -> f a
    R b -> g b

instance Applicative ((|>) a) where
  pure = R
  (<*>) = ap

instance Monad ((|>) a) where
  (>>=) = flip (exlr inl)

(|>) :: (os -> r) -> (o -> r) -> ((os |> o) -> r)
(|>) = exlr


data Γ = Γ
  deriving (Eq, Ord, Show)


data Δ


-- Core rules

class Core s where
  (>>>) :: s r i (o |> a) -> s r (a <| i) o -> s r i o

  init :: s r (a <| i) (o |> a)

infixr 1 >>>

instance Core Seq where
  f >>> g = f >>= pure |> pushL g

  init = popL (pure . inr)


class Structural s where
  -- | Pop something off the input context which can later be pushed. Used with 'pushL', this provides a generalized context restructuring facility.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  popL :: (a -> s r i o) -> s r (a <| i) o

  poppedL :: (s r i o -> s r i' o') -> (s r (a <| i) o -> s r (a <| i') o')

  -- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL :: s r (a <| i) o -> a -> s r i o

  popL2 :: (a -> b -> s r i o) -> s r (a <| b <| i) o

  pushL2 :: s r (a <| b <| i) o -> a -> b -> s r i o

  mapL :: (a' -> a) -> s r (a <| i) o -> s r (a' <| i) o


  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR :: ((a -> r) -> s r i o) -> s r i (o |> a)

  poppedR :: (s r i o -> s r i' o') -> (s r i (o |> a) -> s r i' (o' |> a))

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR :: s r i (o |> a) -> ((a -> r) -> s r i o)

  popR2 :: ((a -> r) -> (b -> r) -> s r i o) -> s r i (o |> b |> a)

  pushR2 :: s r i (o |> b |> a) -> (a -> r) -> (b -> r) -> s r i o

  mapR :: (a -> a') -> s r i (o |> a) -> s r i (o |> a')


  wkL :: s r i o -> s r (a <| i) o
  wkR :: s r i o -> s r i (o |> a)
  cnL :: s r (a <| a <| i) o -> s r (a <| i) o
  cnR :: s r i (o |> a |> a) -> s r i (o |> a)
  exL :: s r (a <| b <| c) o -> s r (b <| a <| c) o
  exR :: s r i (o |> a |> b) -> s r i (o |> b |> a)

  poppedL f p = popL (f . pushL p)
  popL2 f = popL (popL . f)
  pushL2 p = pushL . pushL p
  mapL f p = popL (pushL p . f)
  poppedR f p = popR (f . pushR p)
  popR2 f = popR (popR . f)
  pushR2 p = pushR . pushR p
  mapR f p = popR (pushR p . (. f))
  wkL = popL . const
  wkR = popR . const
  cnL = popL . join . pushL2
  cnR = popR . join . pushR2
  exL = popL2 . flip . pushL2
  exR = popR2 . flip . pushR2

instance Structural Seq where
  popL f = sequent $ \ k -> uncurryConj (flip (runSeq k) . f)
  pushL s a = sequent $ \ k i -> runSeq k (a <| i) s

  popR f = sequent $ \ k c -> runSeq (k . inl) c (f (k . inr))
  pushR s a = sequent $ \ k i -> runSeq (k |> a) i s


-- Negating

newtype Not    r a = Not    { getNot    :: K r a }

instance Pos a => Polarized N (Not r a) where


newtype Negate r a = Negate { getNegate :: K r a }

instance Neg a => Polarized P (Negate r a) where


class (Core s, Structural s) => Negative s where
  notL :: Pos a => s r i (o |> a) -> s r (Not r a <| i) o
  notL' :: Pos a => s r (Not r a <| i) o -> s r i (o |> a)
  notR :: Pos a => s r (a <| i) o -> s r i (o |> Not r a)
  notR' :: Pos a => s r i (o |> Not r a) -> s r (a <| i) o

  negateL :: Neg a => s r i (o |> a) -> s r (Negate r a <| i) o
  negateL' :: Neg a => s r (Negate r a <| i) o -> s r i (o |> a)
  negateR :: Neg a => s r (a <| i) o -> s r i (o |> Negate r a)
  negateR' :: Neg a => s r i (o |> Negate r a) -> s r (a <| i) o

  notL' p = notR init >>> wkR p
  notR' p = wkL p >>> notL init
  negateL' p = negateR init >>> wkR p
  negateR' p = wkL p >>> negateL init

instance Negative Seq where
  negateL p = popL (\ negateA -> p >>> liftL (getK (getNegate negateA)))
  negateR = lowerL (liftR . Negate . K) . wkR

  notL p = popL (\ notA -> p >>> liftL (getK (getNot notA)))
  notR = lowerL (liftR . Not . K) . wkR


-- Additive

data Top = Top
  deriving (Eq, Ord, Show)

instance Polarized N Top where


data Zero

instance Polarized P Zero where

absurdP :: Zero -> a
absurdP = \case


newtype a & b = With (forall r . (a -> b -> r) -> r)
  deriving (Functor)

infixr 6 &

instance (Neg a, Neg b) => Polarized N (a & b) where

instance Foldable ((&) f) where
  foldMap = foldMapConj

instance Traversable ((&) f) where
  traverse = traverseConj

instance Conj (&) where
  inlr a b = With $ \ f -> f a b
  exl (With run) = run const
  exr (With run) = run (const id)


data a ⊕ b
  = InL !a
  | InR !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 ⊕

instance (Pos a, Pos b) => Polarized P (a ⊕ b)

instance Disj (⊕) where
  inl = InL
  inr = InR
  exlr ifl ifr = \case
    InL l -> ifl l
    InR r -> ifr r


class (Core s, Structural s, Negative s) => Additive s where
  zeroL :: s r (Zero <| i) o

  topR :: s r i (o |> Top)

  sumL :: (Pos a, Pos b) => s r (a <| i) o -> s r (b <| i) o -> s r (a ⊕ b <| i) o
  sumL1' :: (Pos a, Pos b) => s r (a ⊕ b <| i) o -> s r (a <| i) o
  sumL2' :: (Pos a, Pos b) => s r (a ⊕ b <| i) o -> s r (b <| i) o
  sumLWith :: (Pos a, Pos b) => s r i (o |> Not r a & Not r b) -> s r (a ⊕ b <| i) o
  sumR1 :: (Pos a, Pos b) => s r i (o |> a) -> s r i (o |> a ⊕ b)
  sumR2 :: (Pos a, Pos b) => s r i (o |> b) -> s r i (o |> a ⊕ b)

  withL1 :: (Neg a, Neg b) => s r (a <| i) o -> s r (a & b <| i) o
  withL2 :: (Neg a, Neg b) => s r (b <| i) o -> s r (a & b <| i) o
  withLSum :: (Neg a, Neg b) => s r i (o |> Negate r a ⊕ Negate r b) -> s r (a & b <| i) o
  withR :: (Neg a, Neg b) => s r i (o |> a) -> s r i (o |> b) -> s r i (o |> (a & b))
  withR1' :: (Neg a, Neg b) => s r i (o |> (a & b)) -> s r i (o |> a)
  withR2' :: (Neg a, Neg b) => s r i (o |> (a & b)) -> s r i (o |> b)

  sumL p1 p2 = sumLWith (withR (notR p1) (notR p2))
  sumL1' p = sumR1 init >>> exL (wkL p)
  sumL2' p = sumR2 init >>> exL (wkL p)
  sumLWith p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))
  withL1 = withLSum . sumR1 . negateR
  withL2 = withLSum . sumR2 . negateR
  withLSum p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
  withR1' t = exR (wkR t) >>> withL1 init
  withR2' t = exR (wkR t) >>> withL2 init


instance Additive Seq where
  zeroL = popL absurdP

  topR = pure (inr Top)

  sumL a b = popL (exlr (pushL a) (pushL b))
  sumR1 = mapR inl
  sumR2 = mapR inr

  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = liftA2 (liftA2 inlr)


-- Multiplicative

data Bot

instance Polarized N Bot where

absurdN :: Bot -> a
absurdN = \case


data One = One
  deriving (Eq, Ord, Show)

instance Polarized P One where


newtype a ⅋ b = Par (forall r . (a -> r) -> (b -> r) -> r)
  deriving (Functor)

infixr 7 ⅋

instance (Neg a, Neg b) => Polarized N (a ⅋ b) where

instance Foldable ((⅋) f) where
  foldMap = foldMapDisj

instance Traversable ((⅋) f) where
  traverse = traverseDisj

instance Disj (⅋) where
  inl l = Par $ \ ifl _ -> ifl l
  inr r = Par $ \ _ ifr -> ifr r
  exlr ifl ifr (Par run) = run ifl ifr


data a ⊗ b = !a :⊗ !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ⊗, :⊗

instance (Pos a, Pos b) => Polarized P (a ⊗ b) where

instance Conj (⊗) where
  inlr = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r


class (Core s, Structural s, Negative s) => Multiplicative s where
  botL :: s r (Bot <| i) o
  botR :: s r i o -> s r i (o |> Bot)
  botR' :: s r i (o |> Bot) -> s r i o

  oneL :: s r i o -> s r (One <| i) o
  oneL' :: s r (One <| i) o -> s r i o
  oneR :: s r i (o |> One)

  parL :: (Neg a, Neg b) => s r (a <| i) o -> s r (b <| i) o -> s r (a ⅋ b <| i) o
  parLTensor :: (Neg a, Neg b) => s r i (o |> Negate r a ⊗ Negate r b) -> s r (a ⅋ b <| i) o
  parR :: (Neg a, Neg b) => s r i (o |> a |> b) -> s r i (o |> a ⅋ b)
  parR' :: (Neg a, Neg b) => s r i (o |> a ⅋ b) -> s r i (o |> a |> b)

  tensorL :: (Pos a, Pos b) => s r (a <| b <| i) o -> s r (a ⊗ b <| i) o
  tensorLPar :: (Pos a, Pos b) => s r i (o |> Not r a ⅋ Not r b) -> s r (a ⊗ b <| i) o
  tensorL' :: (Pos a, Pos b) => s r (a ⊗ b <| i) o -> s r (a <| b <| i) o
  tensorR :: (Pos a, Pos b) => s r i (o |> a) -> s r i (o |> b) -> s r i (o |> a ⊗ b)

  botR' = (>>> botL)
  oneL' = (oneR >>>)
  parL p1 p2 = parLTensor (tensorR (negateR p1) (negateR p2))
  parLTensor p = wkL p >>> tensorL (negateL (negateL (parL (wkR init) init)))
  parR' p = poppedR (wkR . wkR) p >>> parL (wkR init) init
  tensorL = tensorLPar . parR . notR . notR
  tensorLPar p = wkL p >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
  tensorL' p = tensorR init (wkL init) >>> popL (wkL . wkL . pushL p)


instance Multiplicative Seq where
  botL = popL absurdN
  botR = fmap inl

  oneL = wkL
  oneR = pure (inr One)

  parL a b = popL (exlr (pushL a) (pushL b))
  parR ab = (>>= inr . inl) |> inr . inr <$> ab

  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = liftA2 (liftA2 inlr)


-- Implicative

newtype Fun r a b = Fun { getFun :: CPS r a b }

type (-->) = Fun Δ

infixr 5 -->

instance (Pos a, Neg b) => Polarized N (Fun r a b) where

-- runFun :: Fun r a b -> (b -> r) -> a -> r
-- runFun (Fun s) k a = runSeq (either absurdΔ (_)) (Negate _, Γ) s

appFun :: Fun r a b -> Seq r (Negate r b <| i) (o |> Not r a)
appFun (Fun f) = liftLR (Not . getCPS f . getNegate)


data Sub r a b = Sub { subA :: !a, subK :: !(Negate r b) }

type (--<) = Sub Δ

infixr 5 --<

instance (Pos a, Neg b) => Polarized P (Sub r a b) where


class (Core s, Structural s, Negative s) => Implicative s where
  funL :: (Pos a, Neg b) => s r i (o |> a) -> s r (b <| i) o -> s r (Fun r a b <| i) o
  funLSub :: (Pos a, Neg b) => s r i (o |> Sub r a b) -> s r (Fun r a b <| i) o
  funL2 :: (Pos a, Neg b) => s r (Fun r a b <| a <| i)  (o |> b)
  funR :: (Pos a, Neg b) => s r (a <| i) (o |> b) -> s r i (o |> Fun r a b)
  funR' :: (Pos a, Neg b) => s r i (o |> Fun r a b) -> s r (a <| i) (o |> b)

  subL :: (Pos a, Neg b) => s r (a <| i) (o |> b) -> s r (Sub r a b <| i) o
  subLFun :: (Pos a, Neg b) => s r i (o |> Fun r a b) -> s r (Sub r a b <| i) o
  subL' :: (Pos a, Neg b) => s r (Sub r a b <| i) o -> s r (a <| i) (o |> b)
  subR :: (Pos a, Neg b) => s r i (o |> a) -> s r (b <| i) o -> s r i (o |> Sub r a b)

  ($$) :: (Pos a, Neg b) => s r i (o |> Fun r a b) -> s r i (o |> a) -> s r i (o |> b)

  funL pa pb = funLSub (subR pa pb)
  funLSub p = wkL p >>> subL (exL (funL init init))
  funL2 = funL init init
  funR' p = wkL (exR (wkR p)) >>> funL2
  subL = subLFun . funR
  subLFun p = wkL p >>> exL (subL (exL (funL init init)))
  subL' p = subR init init >>> wkR (exL (wkL p))
  f $$ a = exR (wkR f) >>> exR (wkR a) `funL` init


instance Implicative Seq where
  funL a b = popL (\ f -> a >>> notR' (exR (negateL' (appFun f))) >>> exL (wkL b))
  funR = lowerLR (liftR . Fun . cps) . exR . wkR

  subL b = popL (\ s -> pushL b (subA s) >>> pushL (negateL init) (subK s))
  subR a b = liftA2 Sub <$> a <*> negateR b


-- Quantifying

newtype ForAll p f = ForAll { runForAll :: forall x . Polarized p x => f x }

instance (forall x . Polarized n x => Neg (f x)) => Polarized N (ForAll p f)


data Exists p f = forall x . Polarized p x => Exists (f x)

instance (forall x . Polarized n x => Pos (f x)) => Polarized P (Exists p f)

runExists :: (forall x . Polarized p x => f x -> r) -> Exists p f -> r
runExists f (Exists r) = f r


type ForAllC cx cf f = (forall x . cx x => cf (f x)) :: Constraint


class (Core s, Structural s, Negative s, Shifting s) => Quantifying s where
  forAllL :: (Polarized n x, Neg (f x)) => s r (f x <| i) o -> s r (ForAll n f <| i) o
  forAllLExists :: ForAllC (Polarized n) Neg f => s r i (o |> Exists n (Negate r · f)) -> s r (ForAll n f <| i) o
  -- FIXME: the correct signature should be s r i (o |> (forall x . Polarized n x => f x)) -> s r i (o |> ForAll f), but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  -- forAllR :: ForAllC (Polarized n) Neg f => (forall x . Polarized n x => s r i (o |> f x)) -> s r i (o |> ForAll n f)
  forAllR' :: ForAllC (Polarized n) Neg f => s r i (o |> ForAll n f) -> (forall x . Polarized n x => s r i (o |> f x))

  -- FIXME: the correct signature should be s r ((forall x . f x) <| i) o -> s r (Exists f <| i) o, but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  existsL :: (forall x . Polarized n x => s r (f x <| i) o) -> s r (Exists n f <| i) o
  existsL' :: ForAllC (Polarized n) Pos f => s r (Exists n f <| i) o -> (forall x . Polarized n x => s r (f x <| i) o)
  existsLForAll :: ForAllC (Polarized n) Pos f => s r i (o |> ForAll n (Not r · f)) -> s r (Exists n f <| i) o
  existsR :: (Polarized n x, Pos (f x)) => s r i (o |> f x) -> s r i (o |> Exists n f)

  forAllLExists p = wkL p >>> existsL (mapL getC (negateL (forAllL init)))
  forAllR' p = exR (wkR p) >>> forAllL init
  existsL' p = existsR init >>> exL (wkL p)
  existsLForAll p = wkL p >>> exL (existsL (exL (forAllL (mapL getC (notL init)))))


instance Quantifying Seq where
  forAllL p = mapL runForAll p
  -- forAllR p = mapR ForAll p

  existsL p = popL (runExists (pushL p))
  existsR p = mapR Exists p


-- Recursive

newtype Nu r f = Nu { getNu :: Exists P (NuF r f) }

instance Polarized N (Nu r f) where

newtype NuF r f a = NuF { getNuF :: Down (Fun r a (f a)) ⊗ a }

instance (Polarized N (f a), Polarized P a) => Polarized P (NuF r f a)


newtype Mu r f = Mu { getMu :: ForAll N (MuF r f) }

instance ForAllC Neg Pos f => Polarized N (Mu r f) where

newtype MuF r f a = MuF { getMuF :: Fun r (Down (Fun r (f a) a)) a }

instance (Polarized P (f a), Polarized N a) => Polarized N (MuF r f a) where


-- foldMu :: (f a -> a) -> Mu f -> a
-- foldMu alg (Mu (ForAll (MuF (Fun f)))) = f alg

-- unfoldMu :: Functor f => (a -> f a) -> a -> Mu f
-- unfoldMu coalg a = Mu $ ForAll $ MuF $ \ alg -> refold alg coalg a

-- refoldMu :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
-- refoldMu f g = foldMu f . unfoldMu g

-- mu :: Functor f => f (Mu f) -> Mu f
-- mu = unfoldMu (fmap getMu)

-- runMu :: Functor f => Mu f -> f (Mu f)
-- runMu = foldMu (fmap mu)

-- nuToMu :: Functor f => Nu f -> Mu f
-- nuToMu = unfoldMu getNu


class (Core s, Structural s, Implicative s, Quantifying s) => Recursive s where
  nuL :: ForAllC (Polarized P) Neg f => s r (Exists P (NuF r f) <| i) o -> s r (Nu r f <| i) o
  nuR :: ForAllC (Polarized P) Neg f => s r i (o |> Exists P (NuF r f)) -> s r i (o |> Nu r f)
  nuR' :: ForAllC (Polarized P) Neg f => s r i (o |> Nu r f) -> s r i (o |> Exists P (NuF r f))

  muL :: ForAllC (Polarized N) Pos f => s r (ForAll N (MuF r f) <| i) o -> s r (Mu r f <| i) o
  muL' :: ForAllC (Polarized N) Pos f => s r (Mu r f <| i) o -> s r (ForAll N (MuF r f) <| i) o
  muR :: ForAllC (Polarized N) Pos f => s r i (o |> ForAll N (MuF r f)) -> s r i (o |> Mu r f)
  muLFold :: (ForAllC (Polarized N) Pos f, Neg a) => s r i (o |> Fun r (f a) a) -> s r i (o |> Mu r f) -> s r i (o |> a)

  nuR' p = exR (wkR p) >>> nuL init
  muL' p = muR init >>> exL (wkL p)
  muLFold f mu = exR (wkR mu) >>> muL (forAllL (mapL getMuF (funL (downR (exR (wkR f))) init)))


instance Recursive Seq where
  muL = mapL getMu
  muR = mapR Mu

  nuL = mapL getNu
  nuR = mapR Nu


-- Polarity

newtype N a = N { getN :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity


newtype P a = P { getP :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity


class Polarity p where
  polarize' :: a -> p a

instance Polarity N where
  polarize' = N

instance Polarity P where
  polarize' = P


class Polarized p c | c -> p where
  polarize :: c -> p c
  default polarize :: Polarity p => c -> p c
  polarize = polarize'

instance Polarized N (N a)
instance Polarized P (P a)

type Neg = Polarized N
type Pos = Polarized P

neg :: Neg a => a -> a
neg = getN . polarize

pos :: Pos a => a -> a
pos = getP . polarize


up :: Pos a => a -> Up a
up = Up . pos

runUp :: Pos a => Up a -> a
runUp = pos . getUp

newtype Up   a = Up   { getUp   :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Pos a => Polarized N (Up a) where


down :: Neg a => a -> Down a
down = Down . neg

runDown :: Neg a => Down a -> a
runDown = neg . getDown

newtype Down a = Down { getDown :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Neg a => Polarized P (Down a) where


class (Core s, Structural s) => Shifting s where
  upL   :: Pos a => s r (a <| i) o -> s r (Up   a <| i) o
  upL'   :: Pos a => s r (Up   a <| i) o -> s r (a <| i) o
  upR   :: Pos a => s r i (o |> a) -> s r i (o |> Up   a)
  upR'   :: Pos a => s r i (o |> Up   a) -> s r i (o |> a)

  downL :: Neg a => s r (a <| i) o -> s r (Down a <| i) o
  downL'   :: Neg a => s r (Down a <| i) o -> s r (a <| i) o
  downR :: Neg a => s r i (o |> a) -> s r i (o |> Down a)
  downR'   :: Neg a => s r i (o |> Down a) -> s r i (o |> a)

  upL' p = upR init >>> exL (wkL p)
  upR' p = exR (wkR p) >>> upL init
  downL' p = downR init >>> exL (wkL p)
  downR' p = exR (wkR p) >>> downL init


instance Shifting Seq where
  upL   = mapL runUp
  upR   = mapR up

  downL = mapL runDown
  downR = mapR down


-- Utilities

mapK :: (a' -> a) -> K r a -> K r a'
mapK f (K g) = K (g . f)

runK :: a -> K r a -> r
runK = flip getK

newtype K r a = K { getK :: a -> r }

instance Cat.Category K where
  id = K id
  K f . K g = K (g . f)


cps :: ((b -> r) -> (a -> r)) -> CPS r a b
cps f = CPS (K . f . getK)

liftCPS :: (a -> b) -> CPS r a b
liftCPS f = CPS (\ k -> K (getK k . f))

runCPS :: (b -> r) -> a -> CPS r a b -> r
runCPS k a c = runK a (getCPS c (K k))

newtype CPS r a b = CPS { getCPS :: K r b -> K r a }

instance Cat.Category (CPS r) where
  id = CPS id
  CPS f . CPS g = CPS (g . f)

instance Functor (CPS r a) where
  fmap f (CPS r) = CPS (r . mapK f)

instance Applicative (CPS r a) where
  pure a = CPS (K . const . runK a)
  (<*>) = ap

instance Monad (CPS r a) where
  r >>= f = cps $ \ k a -> runCPS (runCPS k a . f) a r


newtype (f · g) a = C { getC :: f (g a) }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ·

instance (Polarity p, Polarized p (f (g a))) => Polarized p ((f · g) a) where

instance (Applicative f, Applicative g) => Applicative (f · g) where
  pure = C . pure . pure
  f <*> a = C ((<*>) <$> getC f <*> getC a)


class Conj c where
  inlr :: a -> b -> (a `c` b)
  exl :: (a `c` b) -> a
  exr :: (a `c` b) -> b

instance Conj (,) where
  inlr = (,)
  exl = fst
  exr = snd

curryConj :: Conj p => ((a `p` b) -> r) -> (a -> b -> r)
curryConj f = fmap f . inlr

uncurryConj :: Conj p => (a -> b -> r) -> ((a `p` b) -> r)
uncurryConj f = f <$> exl <*> exr

foldMapConj :: Conj p => (b -> m) -> (a `p` b) -> m
foldMapConj f = f . exr

traverseConj :: (Conj p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseConj f c = inlr (exl c) <$> f (exr c)


class Disj d where
  inl :: a -> (a `d` b)
  inr :: b -> (a `d` b)
  exlr :: (a -> r) -> (b -> r) -> ((a `d` b) -> r)

instance Disj Either where
  inl = Left
  inr = Right
  exlr = either

foldMapDisj :: (Disj p, Monoid m) => (b -> m) -> (a `p` b) -> m
foldMapDisj = exlr (const mempty)

traverseDisj :: (Disj p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseDisj f = exlr (pure . inl) (fmap inr . f)
