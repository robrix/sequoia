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
, liftLR
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
, Sub(..)
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
, Polarized
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
, lowerCPS
, runCPS
, mapCPS
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
import           Data.Kind (Constraint, Type)
import           Data.Void
import           Prelude hiding (init)

-- Sequents

runSeq :: (o -> r) -> i -> Seq r i o -> r
runSeq k c = runCPS k c . getSeq

sequent :: ((o -> r) -> (i -> r)) -> Seq r i o
sequent = Seq . liftCPS

newtype Seq r i o = Seq { getSeq :: CPS r i o }
  deriving (Applicative, Functor, Monad)

liftLR :: CPS r a b -> Seq r (a <| i) (o |> b)
liftLR = Seq . mapCPS exl inr


lowerLR :: (CPS r a b -> Seq r i o) -> Seq r (a <| i) (o |> b) -> Seq r i o
lowerLR f p = sequent $ \ k c -> runSeq k c (f (liftCPS (\ kb a -> runSeq (k |> kb) (a <| c) p)))


-- Effectful sequents

runSeqT :: (o -> m r) -> i -> SeqT r i m o -> m r
runSeqT k i = runSeq k i . getSeqT

newtype SeqT r i m o = SeqT { getSeqT :: Seq (m r) i o }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r i) where
  lift m = SeqT (Seq (liftCPS (\ k _ -> m >>= k)))


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

-- | Discrimination of values in '|>'.
--
-- @¬A ✕ ¬B -> ¬(A + B)@
(|>) :: (os -> r) -> (o -> r) -> ((os |> o) -> r)
(|>) = exlr


data Γ = Γ
  deriving (Eq, Ord, Show)


data Δ


-- Core rules

class (forall r i . Functor (s r i)) => Core s where
  (>>>) :: s r i (o |> a) -> s r (a <| i) o -> s r i o

  init :: s r (a <| i) (o |> a)

infixr 1 >>>

instance Core Seq where
  f >>> g = f >>= pure |> pushL g

  init = popL liftR


class Core s => Structural s where
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
  poppedL f p = popL (f . pushL p)

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
  popL2 f = popL (popL . f)

  pushL2 :: s r (a <| b <| i) o -> a -> b -> s r i o
  pushL2 p = pushL . pushL p

  mapL :: (a' -> a) -> s r (a <| i) o -> s r (a' <| i) o
  mapL f p = popL (pushL p . f)

  liftL :: K r a -> s r (a <| i) o

  lowerL :: (K r a -> s r i o) -> s r (a <| i) o -> s r i o
  lowerL k p = popR k >>> p


  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR :: (K r a -> s r i o) -> s r i (o |> a)

  poppedR :: (s r i o -> s r i' o') -> (s r i (o |> a) -> s r i' (o' |> a))
  poppedR f p = popR (f . pushR p)

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR :: s r i (o |> a) -> (K r a -> s r i o)

  popR2 :: (K r a -> K r b -> s r i o) -> s r i (o |> b |> a)
  popR2 f = popR (popR . f)

  pushR2 :: s r i (o |> b |> a) -> K r a -> K r b -> s r i o
  pushR2 p = pushR . pushR p

  mapR :: (a -> a') -> s r i (o |> a) -> s r i (o |> a')
  mapR f p = popR (pushR p . mapK f)

  liftR :: a -> s r i (o |> a)

  lowerR :: (a -> s r i o) -> s r i (o |> a) -> s r i o
  lowerR k p = p >>> popL k


  wkL :: s r i o -> s r (a <| i) o
  wkL = popL . const
  wkR :: s r i o -> s r i (o |> a)
  wkR = popR . const
  cnL :: s r (a <| a <| i) o -> s r (a <| i) o
  cnL = popL . join . pushL2
  cnR :: s r i (o |> a |> a) -> s r i (o |> a)
  cnR = popR . join . pushR2
  exL :: s r (a <| b <| c) o -> s r (b <| a <| c) o
  exL = popL2 . flip . pushL2
  exR :: s r i (o |> a |> b) -> s r i (o |> b |> a)
  exR = popR2 . flip . pushR2

instance Structural Seq where
  popL f = sequent $ \ k -> uncurryConj (flip (runSeq k) . f)
  pushL s a = sequent $ \ k i -> runSeq k (a <| i) s
  liftL ka = sequent $ \ _ -> getK ka . exl

  popR f = sequent $ \ k c -> runSeq (k . inl) c (f (K (k . inr)))
  pushR s a = sequent $ \ k i -> runSeq (k |> getK a) i s
  liftR = pure . inr


-- Negating

newtype Not    r a = Not    { getNot    :: K r a }

instance Pos a => Polarized N (Not r a) where

instance ToPos a na => Polarize N (K r a) (Not r na) where
  polarize = Not . mapK neutralize
  neutralize = mapK polarize . getNot

instance Pos a => Polarize N (Not r a) (Not r a) where
  polarize = id
  neutralize = id


newtype Negate r a = Negate { getNegate :: K r a }

instance Neg a => Polarized P (Negate r a) where

instance ToNeg a na => Polarize P (K r a) (Negate r na) where
  polarize = Negate . mapK neutralize
  neutralize = mapK polarize . getNegate

instance Neg a => Polarize P (Negate r a) (Negate r a) where
  polarize = id
  neutralize = id


class (Core s, Structural s) => Negative s where
  notL :: Pos a => s r i (o |> a) -> s r (Not r a <| i) o
  notL' :: Pos a => s r (Not r a <| i) o -> s r i (o |> a)
  notL' p = notR init >>> wkR p
  notR :: Pos a => s r (a <| i) o -> s r i (o |> Not r a)
  notR' :: Pos a => s r i (o |> Not r a) -> s r (a <| i) o
  notR' p = wkL p >>> notL init

  negateL :: Neg a => s r i (o |> a) -> s r (Negate r a <| i) o
  negateL' :: Neg a => s r (Negate r a <| i) o -> s r i (o |> a)
  negateL' p = negateR init >>> wkR p
  negateR :: Neg a => s r (a <| i) o -> s r i (o |> Negate r a)
  negateR' :: Neg a => s r i (o |> Negate r a) -> s r (a <| i) o
  negateR' p = wkL p >>> negateL init

instance Negative Seq where
  negateL p = popL (\ negateA -> p >>> liftL (getNegate negateA))
  negateR = lowerL (liftR . Negate) . wkR

  notL p = popL (\ notA -> p >>> liftL (getNot notA))
  notR = lowerL (liftR . Not) . wkR


-- Additive

data Top = Top
  deriving (Eq, Ord, Show)

instance Polarized N Top where

instance Polarize N () Top where
  polarize = const Top
  neutralize = const ()

instance Polarize N Top Top where
  polarize = id
  neutralize = id


data Zero

instance Polarized P Zero where

instance Polarize P Void Zero where
  polarize = absurd
  neutralize = absurdP

instance Polarize P Zero Zero where
  polarize = id
  neutralize = id

absurdP :: Zero -> a
absurdP = \case


newtype a & b = With (forall r . (a -> b -> r) -> r)
  deriving (Functor)

infixr 6 &

instance (Neg a, Neg b) => Polarized N (a & b) where

instance (ToNeg a pa, ToNeg b pb) => Polarize N (a, b) (pa & pb) where
  polarize = inlr <$> polarize . exl <*> polarize . exr
  neutralize = inlr <$> neutralize . exl <*> neutralize . exr

instance (Neg a, Neg b) => Polarize N (a & b) (a & b) where
  polarize = id
  neutralize = id

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

instance (ToPos a pa, ToPos b pb) => Polarize P (a, b) (pa ⊗ pb) where
  polarize = inlr <$> polarize . exl <*> polarize . exr
  neutralize = inlr <$> neutralize . exl <*> neutralize . exr

instance (Pos a, Pos b) => Polarize P (a ⊗ b) (a ⊗ b) where
  polarize = id
  neutralize = id

instance Disj (⊕) where
  inl = InL
  inr = InR
  exlr ifl ifr = \case
    InL l -> ifl l
    InR r -> ifr r


class (Core s, Structural s, Negative s) => Additive s where
  zeroL :: s r (Zero <| i) o
  zeroL = popL absurdP

  topR :: s r i (o |> Top)
  topR = liftR Top

  sumL :: (Pos a, Pos b) => s r (a <| i) o -> s r (b <| i) o -> s r (a ⊕ b <| i) o
  sumL p1 p2 = sumLWith (withR (notR p1) (notR p2))
  sumL1' :: (Pos a, Pos b) => s r (a ⊕ b <| i) o -> s r (a <| i) o
  sumL1' p = sumR1 init >>> exL (wkL p)
  sumL2' :: (Pos a, Pos b) => s r (a ⊕ b <| i) o -> s r (b <| i) o
  sumL2' p = sumR2 init >>> exL (wkL p)
  sumLWith :: (Pos a, Pos b) => s r i (o |> Not r a & Not r b) -> s r (a ⊕ b <| i) o
  sumLWith p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))
  sumR1 :: (Pos a, Pos b) => s r i (o |> a) -> s r i (o |> a ⊕ b)
  sumR2 :: (Pos a, Pos b) => s r i (o |> b) -> s r i (o |> a ⊕ b)

  withL1 :: (Neg a, Neg b) => s r (a <| i) o -> s r (a & b <| i) o
  withL1 = withLSum . sumR1 . negateR
  withL2 :: (Neg a, Neg b) => s r (b <| i) o -> s r (a & b <| i) o
  withL2 = withLSum . sumR2 . negateR
  withLSum :: (Neg a, Neg b) => s r i (o |> Negate r a ⊕ Negate r b) -> s r (a & b <| i) o
  withLSum p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
  withR :: (Neg a, Neg b) => s r i (o |> a) -> s r i (o |> b) -> s r i (o |> (a & b))
  withR1' :: (Neg a, Neg b) => s r i (o |> (a & b)) -> s r i (o |> a)
  withR1' t = exR (wkR t) >>> withL1 init
  withR2' :: (Neg a, Neg b) => s r i (o |> (a & b)) -> s r i (o |> b)
  withR2' t = exR (wkR t) >>> withL2 init


instance Additive Seq where
  sumL a b = popL (exlr (pushL a) (pushL b))
  sumR1 = mapR inl
  sumR2 = mapR inr

  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = liftA2 (liftA2 inlr)


-- Multiplicative

data Bot

instance Polarized N Bot where

instance Polarize N Void Bot where
  polarize = absurd
  neutralize = absurdN

instance Polarize N Bot Bot where
  polarize = id
  neutralize = id

absurdN :: Bot -> a
absurdN = \case


data One = One
  deriving (Eq, Ord, Show)

instance Polarized P One where

instance Polarize P () One where
  polarize = const One
  neutralize = const ()

instance Polarize P One One where
  polarize = id
  neutralize = id


newtype a ⅋ b = Par (forall r . (a -> r) -> (b -> r) -> r)
  deriving (Functor)

infixr 7 ⅋

instance (Neg a, Neg b) => Polarized N (a ⅋ b) where

instance (ToNeg a pa, ToNeg b pb) => Polarize N (Either a b) (pa ⅋ pb) where
  polarize = exlr (inl . polarize) (inr . polarize)
  neutralize = exlr (inl . neutralize) (inr . neutralize)

instance (Neg a, Neg b) => Polarize N (a ⅋ b) (a ⅋ b) where
  polarize = id
  neutralize = id

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

instance (ToPos a pa, ToPos b pb) => Polarize P (Either a b) (pa ⊕ pb) where
  polarize = exlr (inl . polarize) (inr . polarize)
  neutralize = exlr (inl . neutralize) (inr . neutralize)

instance (Pos a, Pos b) => Polarize P (a ⊕ b) (a ⊕ b) where
  polarize = id
  neutralize = id

instance Conj (⊗) where
  inlr = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r


class (Core s, Structural s, Negative s) => Multiplicative s where
  botL :: s r (Bot <| i) o
  botL = popL absurdN
  botR :: s r i o -> s r i (o |> Bot)
  botR = fmap inl
  botR' :: s r i (o |> Bot) -> s r i o
  botR' = (>>> botL)

  oneL :: s r i o -> s r (One <| i) o
  oneL = wkL
  oneL' :: s r (One <| i) o -> s r i o
  oneL' = (oneR >>>)
  oneR :: s r i (o |> One)
  oneR = liftR One

  parL :: (Neg a, Neg b) => s r (a <| i) o -> s r (b <| i) o -> s r (a ⅋ b <| i) o
  parL p1 p2 = parLTensor (tensorR (negateR p1) (negateR p2))
  parLTensor :: (Neg a, Neg b) => s r i (o |> Negate r a ⊗ Negate r b) -> s r (a ⅋ b <| i) o
  parLTensor p = wkL p >>> tensorL (negateL (negateL (parL (wkR init) init)))
  parR :: (Neg a, Neg b) => s r i (o |> a |> b) -> s r i (o |> a ⅋ b)
  parR' :: (Neg a, Neg b) => s r i (o |> a ⅋ b) -> s r i (o |> a |> b)
  parR' p = poppedR (wkR . wkR) p >>> parL (wkR init) init

  tensorL :: (Pos a, Pos b) => s r (a <| b <| i) o -> s r (a ⊗ b <| i) o
  tensorL = tensorLPar . parR . notR . notR
  tensorLPar :: (Pos a, Pos b) => s r i (o |> Not r a ⅋ Not r b) -> s r (a ⊗ b <| i) o
  tensorLPar p = wkL p >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
  tensorL' :: (Pos a, Pos b) => s r (a ⊗ b <| i) o -> s r (a <| b <| i) o
  tensorL' p = tensorR init (wkL init) >>> popL (wkL . wkL . pushL p)
  tensorR :: (Pos a, Pos b) => s r i (o |> a) -> s r i (o |> b) -> s r i (o |> a ⊗ b)


instance Multiplicative Seq where
  parL a b = popL (exlr (pushL a) (pushL b))
  parR ab = (>>= inr . inl) |> inr . inr <$> ab

  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = liftA2 (liftA2 inlr)


-- Implicative

newtype Fun r a b = Fun { getFun :: CPS r a b }

instance (Pos a, Neg b) => Polarized N (Fun r a b) where

instance (ToPos a pa, ToNeg b nb) => Polarize N (CPS r a b) (Fun r pa nb) where
  polarize = Fun . mapCPS neutralize polarize
  neutralize = mapCPS polarize neutralize . getFun

instance (Pos a, Neg b) => Polarize N (Fun r a b) (Fun r a b) where
  polarize = id
  neutralize = id

appFun :: Fun r a b -> Seq r (a <| i) (o |> b)
appFun = Seq . mapCPS exl inr . getFun


data Sub r a b = Sub { subA :: !a, subK :: !(Negate r b) }

instance (Pos a, Neg b) => Polarized P (Sub r a b) where

instance (Pos a, Neg b) => Polarize P (Sub r a b) (Sub r a b) where
  polarize = id
  neutralize = id


class (Core s, Structural s, Negative s) => Implicative s where
  funL :: (Pos a, Neg b) => s r i (o |> a) -> s r (b <| i) o -> s r (Fun r a b <| i) o
  funL pa pb = funLSub (subR pa pb)
  funLSub :: (Pos a, Neg b) => s r i (o |> Sub r a b) -> s r (Fun r a b <| i) o
  funLSub p = wkL p >>> subL (exL (funL init init))
  funL2 :: (Pos a, Neg b) => s r (Fun r a b <| a <| i)  (o |> b)
  funL2 = funL init init
  funR :: (Pos a, Neg b) => s r (a <| i) (o |> b) -> s r i (o |> Fun r a b)
  ($$) :: (Pos a, Neg b) => s r i (o |> Fun r a b) -> s r i (o |> a) -> s r i (o |> b)
  f $$ a = exR (wkR f) >>> exR (wkR a) `funL` init
  funR' :: (Pos a, Neg b) => s r i (o |> Fun r a b) -> s r (a <| i) (o |> b)
  funR' p = wkL (exR (wkR p)) >>> funL2

  subL :: (Pos a, Neg b) => s r (a <| i) (o |> b) -> s r (Sub r a b <| i) o
  subL = subLFun . funR
  subLFun :: (Pos a, Neg b) => s r i (o |> Fun r a b) -> s r (Sub r a b <| i) o
  subLFun p = wkL p >>> exL (subL (exL (funL init init)))
  subL' :: (Pos a, Neg b) => s r (Sub r a b <| i) o -> s r (a <| i) (o |> b)
  subL' p = subR init init >>> wkR (exL (wkL p))
  subR :: (Pos a, Neg b) => s r i (o |> a) -> s r (b <| i) o -> s r i (o |> Sub r a b)


instance Implicative Seq where
  funL a b = popL (\ f -> a >>> appFun f >>> exL (wkL b))
  funR = lowerLR (liftR . Fun) . exR . wkR

  subL b = popL (\ s -> liftR (subA s) >>> b >>> liftL (getNegate (subK s)))
  subR a b = liftA2 Sub <$> a <*> negateR b


-- Quantifying

newtype ForAll p f = ForAll { runForAll :: forall x . Polarized p x => f x }

instance Polarized N (ForAll p f)


data Exists p f = forall x . Polarized p x => Exists (f x)

instance Polarized P (Exists p f)

runExists :: (forall x . Polarized p x => f x -> r) -> Exists p f -> r
runExists f (Exists r) = f r


type ForAllC cx cf f = (forall x . cx x => cf (f x)) :: Constraint


class (Core s, Structural s, Negative s, Shifting s) => Quantifying s where
  forAllL :: (Polarized n x, Neg (f x)) => s r (f x <| i) o -> s r (ForAll n f <| i) o
  forAllLExists :: ForAllC (Polarized n) Neg f => s r i (o |> Exists n (Negate r · f)) -> s r (ForAll n f <| i) o
  forAllLExists p = wkL p >>> existsL (mapL getC (negateL (forAllL init)))
  -- FIXME: the correct signature should be s r i (o |> (forall x . Polarized n x => f x)) -> s r i (o |> ForAll f), but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  -- forAllR :: ForAllC (Polarized n) Neg f => (forall x . Polarized n x => s r i (o |> f x)) -> s r i (o |> ForAll n f)
  forAllR' :: ForAllC (Polarized n) Neg f => s r i (o |> ForAll n f) -> (forall x . Polarized n x => s r i (o |> f x))
  forAllR' p = exR (wkR p) >>> forAllL init

  -- FIXME: the correct signature should be s r ((forall x . f x) <| i) o -> s r (Exists f <| i) o, but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  existsL :: (forall x . Polarized n x => s r (f x <| i) o) -> s r (Exists n f <| i) o
  existsL' :: ForAllC (Polarized n) Pos f => s r (Exists n f <| i) o -> (forall x . Polarized n x => s r (f x <| i) o)
  existsL' p = existsR init >>> exL (wkL p)
  existsLForAll :: ForAllC (Polarized n) Pos f => s r i (o |> ForAll n (Not r · f)) -> s r (Exists n f <| i) o
  existsLForAll p = wkL p >>> exL (existsL (exL (forAllL (mapL getC (notL init)))))
  existsR :: (Polarized n x, Pos (f x)) => s r i (o |> f x) -> s r i (o |> Exists n f)


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

instance Polarized N (Mu r f) where

newtype MuF r f a = MuF { getMuF :: Fun r (Down (Fun r (f a) a)) a }

instance (Polarized P (f a), Polarized N a) => Polarized N (MuF r f a) where


class (Core s, Structural s, Implicative s, Quantifying s) => Recursive s where
  nuL :: ForAllC (Polarized P) Neg f => s r (Exists P (NuF r f) <| i) o -> s r (Nu r f <| i) o
  nuR :: ForAllC (Polarized P) Neg f => s r i (o |> Exists P (NuF r f)) -> s r i (o |> Nu r f)
  nuR' :: ForAllC (Polarized P) Neg f => s r i (o |> Nu r f) -> s r i (o |> Exists P (NuF r f))
  nuR' p = exR (wkR p) >>> nuL init

  muL :: ForAllC (Polarized N) Pos f => s r (ForAll N (MuF r f) <| i) o -> s r (Mu r f <| i) o
  muL' :: ForAllC (Polarized N) Pos f => s r (Mu r f <| i) o -> s r (ForAll N (MuF r f) <| i) o
  muL' p = muR init >>> exL (wkL p)
  muR :: ForAllC (Polarized N) Pos f => s r i (o |> ForAll N (MuF r f)) -> s r i (o |> Mu r f)
  muLFold :: (ForAllC (Polarized N) Pos f, Neg a) => s r i (o |> Fun r (f a) a) -> s r (a <| i) o -> s r (Mu r f <| i) o
  muLFold f k = muL (forAllL (mapL getMuF (funL (downR (exR (wkR f))) init))) >>> exL (wkL k)


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


class Polarized (p :: Type -> Type) c | c -> p
instance Polarized N (N a)
instance Polarized P (P a)
instance (Pos a, Neg b) => Polarized N (a -> b)

type Neg = Polarized N
type Pos = Polarized P


class Polarized p out => Polarize p inn out | inn p -> out, inn out -> p where
  polarize :: inn -> out
  neutralize :: out -> inn

type ToNeg = Polarize N
type ToPos = Polarize P

instance (ToPos a pa, ToNeg b nb) => Polarize N (a -> b) (pa -> nb) where
  polarize f = polarize . f . neutralize
  neutralize f = neutralize . f . polarize

instance (ToPos a pa, ToNeg b nb) => Polarize P (a -> b) (Down (pa -> nb)) where
  polarize f = Down (polarize . f . neutralize)
  neutralize f = neutralize . getDown f . polarize


newtype Up   a = Up   { getUp   :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Pos a => Polarized N (Up a) where

instance Pos a => Polarize N (Up a) (Up a) where
  polarize = id
  neutralize = id


newtype Down a = Down { getDown :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Neg a => Polarized P (Down a) where

instance Neg a => Polarize P (Down a) (Down a) where
  polarize = id
  neutralize = id


class (Core s, Structural s) => Shifting s where
  upL   :: Pos a => s r (a <| i) o -> s r (Up   a <| i) o
  upL'   :: Pos a => s r (Up   a <| i) o -> s r (a <| i) o
  upL' p = upR init >>> exL (wkL p)
  upR   :: Pos a => s r i (o |> a) -> s r i (o |> Up   a)
  upR'   :: Pos a => s r i (o |> Up   a) -> s r i (o |> a)
  upR' p = exR (wkR p) >>> upL init

  downL :: Neg a => s r (a <| i) o -> s r (Down a <| i) o
  downL'   :: Neg a => s r (Down a <| i) o -> s r (a <| i) o
  downL' p = downR init >>> exL (wkL p)
  downR :: Neg a => s r i (o |> a) -> s r i (o |> Down a)
  downR'   :: Neg a => s r i (o |> Down a) -> s r i (o |> a)
  downR' p = exR (wkR p) >>> downL init


instance Shifting Seq where
  upL   = mapL getUp
  upR   = mapR Up

  downL = mapL getDown
  downR = mapR Down


-- Utilities

mapK :: (a' -> a) -> K r a -> K r a'
mapK f (K g) = K (g . f)

runK :: a -> K r a -> r
runK = flip getK

newtype K r a = K { getK :: a -> r }

instance Cat.Category K where
  id = K id
  K f . K g = K (g . f)


cps :: (a -> b) -> CPS r a b
cps f = CPS (\ k -> K (getK k . f))

liftCPS :: ((b -> r) -> (a -> r)) -> CPS r a b
liftCPS f = CPS (K . f . getK)

lowerCPS :: CPS r a b -> ((b -> r) -> (a -> r))
lowerCPS c = getK . getCPS c . K

runCPS :: (b -> r) -> a -> CPS r a b -> r
runCPS k a c = runK a (getCPS c (K k))

-- | CPS is a Profunctor.
mapCPS :: (a' -> a) -> (b -> b') -> CPS r a b -> CPS r a' b'
mapCPS f g (CPS c) = CPS (mapK f . c . mapK g)

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
  r >>= f = liftCPS $ \ k a -> runCPS (runCPS k a . f) a r


newtype (f · g) a = C { getC :: f (g a) }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ·

instance Polarized p (f (g a)) => Polarized p ((f · g) a) where

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
