{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( -- * Sequents
  runSeq
, runSeqIO
, Seq(..)
, liftL
, liftR
, liftLR
, lowerL
, lowerR
, lowerLR
  -- * Contexts
, type (<|)
, type (|>)
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
, I(..)
, Conj(..)
, Disj(..)
) where

import Control.Applicative (liftA2)
import Control.Exception (Exception, catch, throw)
import Control.Monad (ap, join)
import Data.Bifunctor (Bifunctor(..))
import Data.Distributive
import Data.Functor.Adjunction hiding (splitL)
import Data.Functor.Identity
import Data.Functor.Rep
import Data.Kind (Constraint)
import Data.Profunctor hiding ((:->))
import Prelude hiding (init)

-- Sequents

runSeq :: (o -> r) -> i -> Seq r i o -> r
runSeq k c (Seq run) = run k c

runSeqIO :: (o -> IO ()) -> i -> Seq Δ i o -> IO ()
runSeqIO k i (Seq run) = absurdΔ (run (throw . Escape . k) i) `catch` getEscape

newtype Escape = Escape { getEscape :: IO () }

instance Show Escape where show _ = "Escape"
instance Exception Escape


newtype Seq r i o = Seq ((o -> r) -> (i -> r))
  deriving (Functor)

instance Applicative (Seq r i) where
  pure a = Seq $ \ k _ -> k a
  (<*>) = ap

instance Monad (Seq r i) where
  Seq a >>= f = Seq $ \ k c -> a (runSeq k c . f) c

instance Profunctor (Seq r) where
  dimap f g (Seq run) = Seq (\ k -> run (k . g) . f)

liftL :: (a -> r) -> Seq r (a <| i) o
liftL ka = Seq $ \ _ -> ka . fst

liftR :: a -> Seq r i (o |> a)
liftR = pure . pure

liftLR :: (a -> b) -> Seq r (a <| i) (o |> b)
liftLR f = Seq $ \ k -> k . pure . f . fst

lowerL :: ((a -> r) -> Seq r i o) -> Seq r (a <| i) o -> Seq r i o
lowerL f p = Seq $ \ k c -> runSeq k c (f (\ a -> runSeq k (a, c) p))

lowerR :: Structural p => (a -> p r i o) -> p r i (o |> a) -> p r i o
lowerR k p = p >>> popL k

lowerLR :: (((b -> r) -> (a -> r)) -> Seq r i o) -> Seq r (a <| i) (o |> b) -> Seq r i o
lowerLR f p = Seq $ \ k c -> runSeq k c (f (\ kb a -> runSeq (either k kb) (a, c) p))


-- Contexts

type (<|) = (,)
infixr 4 <|

type (|>) = Either
infixl 4 |>

split :: (o |> a -> r) -> (o -> r, a -> r)
split f = (f . Left, f . Right)


data Γ = Γ
  deriving (Eq, Ord, Show)


data Δ

absurdΔ :: Δ -> a
absurdΔ = \case


class AppendL c1 c2 res | c1 c2 -> res, c1 res -> c2 where
  appendL :: c1 -> c2 -> res
  splitL :: res -> (c1, c2)

  instantiateL :: (Structural p, Profunctor p) => c1 `p` o -> res `p` o

instance AppendL Γ ds ds where
  appendL _ = id
  splitL = (Γ,)

  instantiateL = lmap (const Γ)

instance AppendL cs ds res => AppendL (c, cs) ds (c, res) where
  appendL (c, cs) ds = (c, appendL cs ds)
  splitL (c, res) = let (cs, ds) = splitL res in ((c, cs), ds)

  instantiateL = poppedL instantiateL


-- Core rules

class Core s where
  (>>>) :: s i (o |> a) -> s (a <| i) o -> s i o

  init :: s (a <| i) (o |> a)

infixr 1 >>>

instance Core (Seq Δ) where
  f >>> g = f >>= either pure (pushL g)

  init = popL (pure . pure)


class Structural s where
  -- | Pop something off the input context which can later be pushed. Used with 'pushL', this provides a generalized context restructuring facility.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  popL :: (a -> s i o) -> s (a <| i) o

  poppedL :: (s i o -> s i' o') -> (s (a <| i) o -> s (a <| i') o')

  -- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL :: s (a <| i) o -> a -> s i o

  popL2 :: (a -> b -> s i o) -> s (a <| b <| i) o

  pushL2 :: s (a <| b <| i) o -> a -> b -> s i o

  mapL :: (a' -> a) -> s (a <| i) o -> s (a' <| i) o


  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR :: ((a -> Δ) -> s i o) -> s i (o |> a)

  poppedR :: (s i o -> s i' o') -> (s i (o |> a) -> s i' (o' |> a))

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR :: s i (o |> a) -> ((a -> Δ) -> s i o)

  popR2 :: ((a -> Δ) -> (b -> Δ) -> s i o) -> s i (o |> b |> a)

  pushR2 :: s i (o |> b |> a) -> (a -> Δ) -> (b -> Δ) -> s i o

  mapR :: (a -> a') -> s i (o |> a) -> s i (o |> a')


  wkL :: s i o -> s (a <| i) o
  wkR :: s i o -> s i (o |> a)
  cnL :: s (a <| a <| i) o -> s (a <| i) o
  cnR :: s i (o |> a |> a) -> s i (o |> a)
  exL :: s (a <| b <| c) o -> s (b <| a <| c) o
  exR :: s i (o |> a |> b) -> s i (o |> b |> a)

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

instance Structural (Seq Δ) where
  popL f = Seq $ \ k -> uncurry (flip (runSeq k) . f)
  pushL (Seq run) a = Seq $ \ k -> run k . (a,)

  popR f = Seq $ \ k c -> let (k', ka) = split k in runSeq k' c (f ka)
  pushR (Seq run) a = Seq $ \ k -> run (either k a)


-- Negating

newtype Not    r a = Not    { getNot    :: Seq r (a <| Γ) Δ }

instance Pos a => Polarized N (Not r a) where


newtype Negate r a = Negate { getNegate :: Seq r (a <| Γ) Δ }

instance Neg a => Polarized P (Negate r a) where


class (Core s, Structural s) => Negative s where
  notL :: Pos a => s i (o |> a) -> s (Not Δ a <| i) o
  notL' :: Pos a => s (Not Δ a <| i) o -> s i (o |> a)
  notR :: Pos a => s (a <| i) o -> s i (o |> Not Δ a)
  notR' :: Pos a => s i (o |> Not Δ a) -> s (a <| i) o

  negateL :: Neg a => s i (o |> a) -> s (Negate Δ a <| i) o
  negateL' :: Neg a => s (Negate Δ a <| i) o -> s i (o |> a)
  negateR :: Neg a => s (a <| i) o -> s i (o |> Negate Δ a)
  negateR' :: Neg a => s i (o |> Negate Δ a) -> s (a <| i) o

  notL' p = notR init >>> wkR p
  notR' p = wkL p >>> notL init
  negateL' p = negateR init >>> wkR p
  negateR' p = wkL p >>> negateL init

instance Negative (Seq Δ) where
  negateL p = popL (\ negateA -> p >>> dimap (Γ <$) absurdΔ (getNegate negateA))
  negateR p = cont (\ abstract -> Negate (poppedL abstract p))

  notL p = popL (\ notA -> p >>> dimap (Γ <$) absurdΔ (getNot notA))
  notR p = cont (\ abstract -> Not (poppedL abstract p))


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
  zeroL :: s (Zero <| i) o

  topR :: s i (o |> Top)

  sumL :: (Pos a, Pos b) => s (a <| i) o -> s (b <| i) o -> s (a ⊕ b <| i) o
  sumL1' :: (Pos a, Pos b) => s (a ⊕ b <| i) o -> s (a <| i) o
  sumL2' :: (Pos a, Pos b) => s (a ⊕ b <| i) o -> s (b <| i) o
  sumLWith :: (Pos a, Pos b) => s i (o |> Not Δ a & Not Δ b) -> s (a ⊕ b <| i) o
  sumR1 :: (Pos a, Pos b) => s i (o |> a) -> s i (o |> a ⊕ b)
  sumR2 :: (Pos a, Pos b) => s i (o |> b) -> s i (o |> a ⊕ b)

  withL1 :: (Neg a, Neg b) => s (a <| i) o -> s (a & b <| i) o
  withL2 :: (Neg a, Neg b) => s (b <| i) o -> s (a & b <| i) o
  withLSum :: (Neg a, Neg b) => s i (o |> Negate Δ a ⊕ Negate Δ b) -> s (a & b <| i) o
  withR :: (Neg a, Neg b) => s i (o |> a) -> s i (o |> b) -> s i (o |> (a & b))
  withR1' :: (Neg a, Neg b) => s i (o |> (a & b)) -> s i (o |> a)
  withR2' :: (Neg a, Neg b) => s i (o |> (a & b)) -> s i (o |> b)

  sumL p1 p2 = sumLWith (withR (notR p1) (notR p2))
  sumL1' p = sumR1 init >>> exL (wkL p)
  sumL2' p = sumR2 init >>> exL (wkL p)
  sumLWith p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))
  withL1 = withLSum . sumR1 . negateR
  withL2 = withLSum . sumR2 . negateR
  withLSum p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
  withR1' t = exR (wkR t) >>> withL1 init
  withR2' t = exR (wkR t) >>> withL2 init


instance Additive (Seq Δ) where
  zeroL = popL absurdP

  topR = pure (pure Top)

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
  botL :: s (Bot <| i) o
  botR :: s i o -> s i (o |> Bot)
  botR' :: s i (o |> Bot) -> s i o

  oneL :: s i o -> s (One <| i) o
  oneL' :: s (One <| i) o -> s i o
  oneR :: s i (o |> One)

  parL :: (Neg a, Neg b) => s (a <| i) o -> s (b <| i) o -> s (a ⅋ b <| i) o
  parLTensor :: (Neg a, Neg b) => s i (o |> Negate Δ a ⊗ Negate Δ b) -> s (a ⅋ b <| i) o
  parR :: (Neg a, Neg b) => s i (o |> a |> b) -> s i (o |> a ⅋ b)
  parR' :: (Neg a, Neg b) => s i (o |> a ⅋ b) -> s i (o |> a |> b)

  tensorL :: (Pos a, Pos b) => s (a <| b <| i) o -> s (a ⊗ b <| i) o
  tensorLPar :: (Pos a, Pos b) => s i (o |> Not Δ a ⅋ Not Δ b) -> s (a ⊗ b <| i) o
  tensorL' :: (Pos a, Pos b) => s (a ⊗ b <| i) o -> s (a <| b <| i) o
  tensorR :: (Pos a, Pos b) => s i (o |> a) -> s i (o |> b) -> s i (o |> a ⊗ b)

  botR' = (>>> botL)
  oneL' = (oneR >>>)
  parL p1 p2 = parLTensor (tensorR (negateR p1) (negateR p2))
  parLTensor p = wkL p >>> tensorL (negateL (negateL (parL (wkR init) init)))
  parR' p = poppedR (wkR . wkR) p >>> parL (wkR init) init
  tensorL = tensorLPar . parR . notR . notR
  tensorLPar p = wkL p >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
  tensorL' p = tensorR init (wkL init) >>> popL (wkL . wkL . pushL p)


instance Multiplicative (Seq Δ) where
  botL = popL absurdN
  botR = fmap Left

  oneL = wkL
  oneR = pure (pure One)

  parL a b = popL (exlr (pushL a) (pushL b))
  parR ab = either (>>= (pure . inl)) (pure . inr) <$> ab

  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = liftA2 (liftA2 inlr)


-- Implicative

newtype Fun r a b = Fun { getFun :: Seq r (Negate r b <| Γ) (Δ |> Not r a) }

type (-->) = Fun Δ

infixr 5 -->

instance (Pos a, Neg b) => Polarized N (Fun r a b) where

-- runFun :: Fun r a b -> (b -> r) -> a -> r
-- runFun (Fun s) k a = runSeq (either absurdΔ (_)) (Negate _, Γ) s

appFun :: Fun Δ a b -> Seq Δ (Negate Δ b <| i) (o |> Not Δ a)
appFun = instantiateL . rmap (first absurdΔ) . getFun


data Sub r a b = Sub { subA :: !a, subK :: !(Negate r b) }

type (--<) = Sub Δ

infixr 5 --<

instance (Pos a, Neg b) => Polarized P (Sub r a b) where


class (Core s, Structural s, Negative s) => Implicative s where
  funL :: (Pos a, Neg b) => s i (o |> a) -> s (b <| i) o -> s (a --> b <| i) o
  funLSub :: (Pos a, Neg b) => s i (o |> a --< b) -> s (a --> b <| i) o
  funL2 :: (Pos a, Neg b) => s (a --> b <| a <| i)  (o |> b)
  funR :: (Pos a, Neg b) => s (a <| i) (o |> b) -> s i (o |> a --> b)
  funR' :: (Pos a, Neg b) => s i (o |> a --> b) -> s (a <| i) (o |> b)

  subL :: (Pos a, Neg b) => s (a <| i) (o |> b) -> s (a --< b <| i) o
  subLFun :: (Pos a, Neg b) => s i (o |> a --> b) -> s (a --< b <| i) o
  subL' :: (Pos a, Neg b) => s (a --< b <| i) o -> s (a <| i) (o |> b)
  subR :: (Pos a, Neg b) => s i (o |> a) -> s (b <| i) o -> s i (o |> a --< b)

  ($$) :: (Pos a, Neg b) => s i (o |> a --> b) -> s i (o |> a) -> s i (o |> b)

  funL pa pb = funLSub (subR pa pb)
  funLSub p = wkL p >>> subL (exL (funL init init))
  funL2 = funL init init
  funR' p = wkL (exR (wkR p)) >>> funL2
  subL = subLFun . funR
  subLFun p = wkL p >>> exL (subL (exL (funL init init)))
  subL' p = subR init init >>> wkR (exL (wkL p))
  f $$ a = exR (wkR f) >>> exR (wkR a) `funL` init


instance Implicative (Seq Δ) where
  funL a b = popL (\ f -> a >>> notR' (exR (negateL' (appFun f))) >>> exL (wkL b))
  funR b = cont (\ abstract -> Fun (poppedL (poppedR abstract) (notR (exL (negateL b)))))

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
  forAllL :: (Polarized n x, Neg (f x)) => s (f x <| i) o -> s (ForAll n f <| i) o
  forAllLExists :: ForAllC (Polarized n) Neg f => s i (o |> Exists n (Negate Δ · f)) -> s (ForAll n f <| i) o
  -- FIXME: the correct signature should be s i (o |> (forall x . Polarized n x => f x)) -> s i (o |> ForAll f), but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  -- forAllR :: ForAllC (Polarized n) Neg f => (forall x . Polarized n x => s i (o |> f x)) -> s i (o |> ForAll n f)
  forAllR' :: ForAllC (Polarized n) Neg f => s i (o |> ForAll n f) -> (forall x . Polarized n x => s i (o |> f x))

  -- FIXME: the correct signature should be s ((forall x . f x) <| i) o -> s (Exists f <| i) o, but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  existsL :: (forall x . Polarized n x => s (f x <| i) o) -> s (Exists n f <| i) o
  existsL' :: ForAllC (Polarized n) Pos f => s (Exists n f <| i) o -> (forall x . Polarized n x => s (f x <| i) o)
  existsLForAll :: ForAllC (Polarized n) Pos f => s i (o |> ForAll n (Not Δ · f)) -> s (Exists n f <| i) o
  existsR :: (Polarized n x, Pos (f x)) => s i (o |> f x) -> s i (o |> Exists n f)

  forAllLExists p = wkL p >>> existsL (mapL getC (negateL (forAllL init)))
  forAllR' p = exR (wkR p) >>> forAllL init
  existsL' p = existsR init >>> exL (wkL p)
  existsLForAll p = wkL p >>> exL (existsL (exL (forAllL (mapL getC (notL init)))))


instance Quantifying (Seq Δ) where
  forAllL p = mapL runForAll p
  -- forAllR p = mapR ForAll p

  existsL p = popL (runExists (pushL p))
  existsR p = mapR Exists p


-- Recursive

newtype Nu f = Nu { getNu :: Exists P (NuF f) }

instance Polarized N (Nu f) where

newtype NuF f a = NuF { getNuF :: Down (a --> f a) ⊗ a }

instance (Polarized N (f a), Polarized P a) => Polarized P (NuF f a)


newtype Mu f = Mu { getMu :: ForAll N (MuF f) }

instance ForAllC Neg Pos f => Polarized N (Mu f) where

newtype MuF f a = MuF { getMuF :: Down (f a --> a) --> a }

instance (Polarized P (f a), Polarized N a) => Polarized N (MuF f a) where


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
  nuL :: ForAllC (Polarized P) Neg f => s (Exists P (NuF f) <| i) o -> s (Nu f <| i) o
  nuR :: ForAllC (Polarized P) Neg f => s i (o |> Exists P (NuF f)) -> s i (o |> Nu f)
  nuR' :: ForAllC (Polarized P) Neg f => s i (o |> Nu f) -> s i (o |> Exists P (NuF f))

  muL :: ForAllC (Polarized N) Pos f => s (ForAll N (MuF f) <| i) o -> s (Mu f <| i) o
  muL' :: ForAllC (Polarized N) Pos f => s (Mu f <| i) o -> s (ForAll N (MuF f) <| i) o
  muR :: ForAllC (Polarized N) Pos f => s i (o |> ForAll N (MuF f)) -> s i (o |> Mu f)
  muLFold :: (ForAllC (Polarized N) Pos f, Neg a) => s i (o |> f a --> a) -> s i (o |> Mu f) -> s i (o |> a)

  nuR' p = exR (wkR p) >>> nuL init
  muL' p = muR init >>> exL (wkL p)
  muLFold f mu = exR (wkR mu) >>> muL (forAllL (mapL getMuF (funL (downR (exR (wkR f))) init)))


instance Recursive (Seq Δ) where
  muL = mapL getMu
  muR = mapR Mu

  nuL = mapL getNu
  nuR = mapR Nu


-- Polarity

newtype N a = N { getN :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Distributive N where
  collect f = N . fmap (getN . f)
  distribute = N . fmap getN

instance Adjunction N P where
  unit   =    P .    N
  counit = getP . getN
  leftAdjunct  f =    P . f .    N
  rightAdjunct f = getP . f . getN


newtype P a = P { getP :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Distributive P where
  collect f = P . fmap (getP . f)
  distribute = P . fmap getP

instance Adjunction P N where
  unit   =    N .    P
  counit = getN . getP
  leftAdjunct  f =    N . f .    P
  rightAdjunct f = getN . f . getP


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
  deriving (Applicative, Monad, Representable) via Identity

instance Pos a => Polarized N (Up a) where

instance Distributive Up where
  collect f = Up . fmap (getUp . f)
  distribute = Up . fmap getUp

instance Adjunction Up Down where
  unit   =    Down .    Up
  counit = getDown . getUp
  leftAdjunct  f =    Down . f .    Up
  rightAdjunct f = getDown . f . getUp


down :: Neg a => a -> Down a
down = Down . neg

runDown :: Neg a => Down a -> a
runDown = neg . getDown

newtype Down a = Down { getDown :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Neg a => Polarized P (Down a) where

instance Distributive Down where
  collect f = Down . fmap (getDown . f)
  distribute = Down . fmap getDown

instance Adjunction Down Up where
  unit   =    Up .    Down
  counit = getUp . getDown
  leftAdjunct  f =    Up . f .    Down
  rightAdjunct f = getUp . f . getDown


class (Core p, Structural p) => Shifting p where
  upL   :: Pos a => p (a <| i) o -> p (Up   a <| i) o
  upL'   :: Pos a => p (Up   a <| i) o -> p (a <| i) o
  upL' p = upR init >>> exL (wkL p)
  upR   :: Pos a => p i (o |> a) -> p i (o |> Up   a)
  upR'   :: Pos a => p i (o |> Up   a) -> p i (o |> a)
  upR' p = exR (wkR p) >>> upL init

  downL :: Neg a => p (a <| i) o -> p (Down a <| i) o
  downL'   :: Neg a => p (Down a <| i) o -> p (a <| i) o
  downL' p = downR init >>> exL (wkL p)
  downR :: Neg a => p i (o |> a) -> p i (o |> Down a)
  downR'   :: Neg a => p i (o |> Down a) -> p i (o |> a)
  downR' p = exR (wkR p) >>> downL init


instance Shifting (Seq Δ) where
  upL   = mapL runUp
  upR   = mapR up

  downL = mapL runDown
  downR = mapR down


-- Utilities

cont :: ((Seq r i o -> Seq r Γ Δ) -> a) -> Seq Δ i (o |> a)
cont f = Seq $ \ k -> k . Right . f . (`dimap` (k . Left)) . const


newtype I a = I { getI :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Representable) via Identity

instance (Polarity p, Polarized p a) => Polarized p (I a) where

instance Distributive I where
  collect f  = I . fmap (getI . f)
  distribute = I . fmap  getI

instance Adjunction I I where
  unit   =    I .    I
  counit = getI . getI
  leftAdjunct  f =    I . f .    I
  rightAdjunct f = getI . f . getI


newtype K a b = K { getK :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (Polarity p, Polarized p a) => Polarized p (K a b) where


newtype (f · g) a = C { getC :: f (g a) }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ·

instance (Polarity p, Polarized p (f (g a))) => Polarized p ((f · g) a) where

instance (Applicative f, Applicative g) => Applicative (f · g) where
  pure = C . pure . pure
  f <*> a = C ((<*>) <$> getC f <*> getC a)

instance (Distributive f, Distributive g) => Distributive (f · g) where
  collect f r = C (fmap distribute (collect (getC . f) r))


class Conj c where
  inlr :: a -> b -> (a `c` b)
  exl :: (a `c` b) -> a
  exr :: (a `c` b) -> b

foldMapConj :: Conj p => (b -> m) -> (a `p` b) -> m
foldMapConj f = f . exr

traverseConj :: (Conj p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseConj f c = inlr (exl c) <$> f (exr c)


class Disj d where
  inl :: a -> (a `d` b)
  inr :: b -> (a `d` b)
  exlr :: (a -> r) -> (b -> r) -> ((a `d` b) -> r)

foldMapDisj :: (Disj p, Monoid m) => (b -> m) -> (a `p` b) -> m
foldMapDisj = exlr (const mempty)

traverseDisj :: (Disj p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseDisj f = exlr (pure . inl) (fmap inr . f)
