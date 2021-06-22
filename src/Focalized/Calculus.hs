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
, type (&)
, type (⊕)
, Additive(..)
  -- * Multiplicative
, Bot
, One(..)
, type (⅋)
, type (⊗)
, (:⊗)(..)
, Multiplicative(..)
  -- * Implicative
, type (-->)(..)
, type (--<)(..)
, Implicative(..)
  -- * Quantifying
, ForAll(..)
, Exists(..)
, Quantifying(..)
  -- * Recursive
, Mu(..)
, Nu(..)
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
, J(..)
, (:->)(..)
, Conj(..)
, foldMapConj
, bifoldMapConj
, fmapConj
, bimapConj
, traverseConj
, bitraverseConj
, Disj(..)
, foldMapDisj
, bifoldMapDisj
, fmapDisj
, bimapDisj
, traverseDisj
, bitraverseDisj
) where

import Control.Applicative (liftA2)
import Control.Exception (Exception, catch, throw)
import Control.Monad (ap, join)
import Data.Bifoldable
import Data.Bifunctor (Bifunctor(..))
import Data.Bitraversable
import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Identity
import Data.Functor.Rep
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


-- Core rules

class Core p where
  (>>>) :: p i (o |> a) -> p (a <| i) o -> p i o

  init :: p (a <| i) (o |> a)

infixr 1 >>>

instance Core (Seq Δ) where
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
  popL :: (a -> p i o) -> p (a <| i) o

  poppedL :: (p i o -> p i' o') -> (p (a <| i) o -> p (a <| i') o')
  poppedL f p = popL (f . pushL p)

  -- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL :: p (a <| i) o -> a -> p i o

  popL2 :: (a -> b -> p i o) -> p (a <| b <| i) o
  popL2 f = popL (popL . f)

  pushL2 :: p (a <| b <| i) o -> a -> b -> p i o
  pushL2 p = pushL . pushL p

  mapL :: (a' -> a) -> p (a <| i) o -> p (a' <| i) o
  mapL f p = popL (pushL p . f)


  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR :: ((a -> Δ) -> p i o) -> p i (o |> a)

  poppedR :: (p i o -> p i' o') -> (p i (o |> a) -> p i' (o' |> a))
  poppedR f p = popR (f . pushR p)

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR :: p i (o |> a) -> ((a -> Δ) -> p i o)

  popR2 :: ((a -> Δ) -> (b -> Δ) -> p i o) -> p i (o |> b |> a)
  popR2 f = popR (popR . f)

  pushR2 :: p i (o |> b |> a) -> (a -> Δ) -> (b -> Δ) -> p i o
  pushR2 p = pushR . pushR p

  mapR :: (a -> a') -> p i (o |> a) -> p i (o |> a')
  mapR f p = popR (pushR p . (. f))


  wkL :: p i o -> p (a <| i) o
  wkL = popL . const
  wkR :: p i o -> p i (o |> a)
  wkR = popR . const
  cnL :: p (a <| a <| i) o -> p (a <| i) o
  cnL = popL . join . pushL2
  cnR :: p i (o |> a |> a) -> p i (o |> a)
  cnR = popR . join . pushR2
  exL :: p (a <| b <| c) o -> p (b <| a <| c) o
  exL = popL2 . flip . pushL2
  exR :: p i (o |> a |> b) -> p i (o |> b |> a)
  exR = popR2 . flip . pushR2

instance Structural (Seq Δ) where
  popL f = Seq $ \ k -> uncurry (flip (runSeq k) . f)
  pushL (Seq run) a = Seq $ \ k -> run k . (a,)

  popR f = Seq $ \ k c -> let (k', ka) = split k in runSeq k' c (f ka)
  pushR (Seq run) a = Seq $ \ k -> run (either k a)


-- Negating

newtype Not    a = Not    { getNot    :: Seq Δ (a <| Γ) Δ }

instance Pos a => Polarized N (Not a) where


newtype Negate a = Negate { getNegate :: Seq Δ (a <| Γ) Δ }

instance Neg a => Polarized P (Negate a) where


class (Core p, Structural p) => Negative p where
  notL :: Pos a => p i (o |> a) -> p (Not a <| i) o
  notL' :: Pos a => p (Not a <| i) o -> p i (o |> a)
  notL' p = notR init >>> wkR p
  notR :: Pos a => p (a <| i) o -> p i (o |> Not a)
  notR' :: Pos a => p i (o |> Not a) -> p (a <| i) o
  notR' p = wkL p >>> notL init

  negateL :: Neg a => p i (o |> a) -> p (Negate a <| i) o
  negateL' :: Neg a => p (Negate a <| i) o -> p i (o |> a)
  negateL' p = negateR init >>> wkR p
  negateR :: Neg a => p (a <| i) o -> p i (o |> Negate a)
  negateR' :: Neg a => p i (o |> Negate a) -> p (a <| i) o
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


type (&) = I :& I

infixr 6 &, :&


newtype (f :& g) a b = With1 (forall r . (f a -> g b -> r) -> r)
  deriving (Functor)

instance (Neg (f a), Neg (g b)) => Polarized N ((f :& g) a b) where

instance Foldable g => Foldable ((f :& g) a) where
  foldMap = foldMapConj

instance Traversable g => Traversable ((f :& g) a) where
  traverse = traverseConj

instance (Foldable f, Foldable g) => Bifoldable (f :& g) where
  bifoldMap = bifoldMapConj

instance (Functor f, Functor g) => Bifunctor (f :& g) where
  bimap = bimapConj

instance (Traversable f, Traversable g) => Bitraversable (f :& g) where
  bitraverse = bitraverseConj

instance Conj f g (f :& g) where
  inlr a b = With1 $ \ f -> f a b
  exl (With1 run) = run const
  exr (With1 run) = run (const id)


type (⊕) = I :⊕ I

infixr 6 ⊕, :⊕


data (f :⊕ g) a b
  = InL1 !(f a)
  | InR1 !(g b)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (Pos (f a), Pos (g b)) => Polarized P ((f :⊕ g) a b)

instance (Foldable f, Foldable g) => Bifoldable (f :⊕ g) where
  bifoldMap = bifoldMapDisj

instance (Functor f, Functor g) => Bifunctor (f :⊕ g) where
  bimap = bimapDisj

instance (Traversable f, Traversable g) => Bitraversable (f :⊕ g) where
  bitraverse = bitraverseDisj

instance Disj f g (f :⊕ g) where
  inl = InL1
  inr = InR1
  exlr ifl ifr = \case
    InL1 l -> ifl l
    InR1 r -> ifr r


class (Core p, Structural p, Negative p) => Additive p where
  zeroL :: p (Zero <| i) o

  topR :: p i (o |> Top)

  sumL :: (Pos a, Pos b) => p (a <| i) o -> p (b <| i) o -> p (a ⊕ b <| i) o
  sumL p1 p2 = sumLWith (notR p1 & notR p2)
  sumL1' :: (Pos a, Pos b) => p (a ⊕ b <| i) o -> p (a <| i) o
  sumL1' p = sumR1 init >>> exL (wkL p)
  sumL2' :: (Pos a, Pos b) => p (a ⊕ b <| i) o -> p (b <| i) o
  sumL2' p = sumR2 init >>> exL (wkL p)
  sumLWith :: (Pos a, Pos b) => p i (o |> Not a & Not b) -> p (a ⊕ b <| i) o
  sumLWith p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))
  sumR1 :: (Pos a, Pos b) => p i (o |> a) -> p i (o |> a ⊕ b)
  sumR2 :: (Pos a, Pos b) => p i (o |> b) -> p i (o |> a ⊕ b)

  withL1 :: (Neg a, Neg b) => p (a <| i) o -> p (a & b <| i) o
  withL1 = withLSum . sumR1 . negateR
  withL2 :: (Neg a, Neg b) => p (b <| i) o -> p (a & b <| i) o
  withL2 = withLSum . sumR2 . negateR
  withLSum :: (Neg a, Neg b) => p i (o |> Negate a ⊕ Negate b) -> p (a & b <| i) o
  withLSum p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
  (&) :: (Neg a, Neg b) => p i (o |> a) -> p i (o |> b) -> p i (o |> (a & b))
  withR1' :: (Neg a, Neg b) => p i (o |> (a & b)) -> p i (o |> a)
  withR1' t = exR (wkR t) >>> withL1 init
  withR2' :: (Neg a, Neg b) => p i (o |> (a & b)) -> p i (o |> b)
  withR2' t = exR (wkR t) >>> withL2 init


instance Additive (Seq Δ) where
  zeroL = popL absurdP

  topR = pure (pure Top)

  sumL a b = popL (exlrI (pushL a) (pushL b))
  sumR1 = mapR inlI
  sumR2 = mapR inrI

  withL1 p = popL (pushL p . exlI)
  withL2 p = popL (pushL p . exrI)
  (&) = liftA2 (liftA2 inlrI)


-- Multiplicative

data Bot

instance Polarized N Bot where

absurdN :: Bot -> a
absurdN = \case


data One = One
  deriving (Eq, Ord, Show)

instance Polarized P One where


type (⅋) = I :⅋ I

infixr 7 ⅋, :⅋


newtype (f :⅋ g) a b = Par1 (forall r . (f a -> r) -> (g b -> r) -> r)
  deriving (Functor)

instance (Neg (f a), Neg (g b)) => Polarized N ((f :⅋ g) a b) where

instance Foldable g => Foldable ((f :⅋ g) a) where
  foldMap = foldMapDisj

instance Traversable g => Traversable ((f :⅋ g) a) where
  traverse = traverseDisj

instance (Foldable f, Foldable g) => Bifoldable (f :⅋ g) where
  bifoldMap = bifoldMapDisj

instance (Functor f, Functor g) => Bifunctor (f :⅋ g) where
  bimap = bimapDisj

instance (Traversable f, Traversable g) => Bitraversable (f :⅋ g) where
  bitraverse = bitraverseDisj

instance Disj f g (f :⅋ g) where
  inl l = Par1 $ \ ifl _ -> ifl l
  inr r = Par1 $ \ _ ifr -> ifr r
  exlr ifl ifr (Par1 run) = run ifl ifr


type (⊗) = I :⊗ I

infixr 7 ⊗, :⊗


data (f :⊗ g) a b = !(f a) :⊗ !(g b)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (Pos (f a), Pos (g b)) => Polarized P ((f :⊗ g) a b) where

instance (Foldable f, Foldable g) => Bifoldable (f :⊗ g) where
  bifoldMap = bifoldMapConj

instance (Functor f, Functor g) => Bifunctor (f :⊗ g) where
  bimap = bimapConj

instance (Traversable f, Traversable g) => Bitraversable (f :⊗ g) where
  bitraverse = bitraverseConj

instance Conj f g (f :⊗ g) where
  inlr = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r


class (Core p, Structural p, Negative p) => Multiplicative p where
  botL :: p (Bot <| i) o
  botR :: p i o -> p i (o |> Bot)
  botR' :: p i (o |> Bot) -> p i o
  botR' = (>>> botL)

  oneL :: p i o -> p (One <| i) o
  oneL' :: p (One <| i) o -> p i o
  oneL' = (oneR >>>)
  oneR :: p i (o |> One)

  parL :: (Neg a, Neg b) => p (a <| i) o -> p (b <| i) o -> p (a ⅋ b <| i) o
  parL p1 p2 = parLTensor (negateR p1 ⊗ negateR p2)
  parLTensor :: (Neg a, Neg b) => p i (o |> Negate a ⊗ Negate b) -> p (a ⅋ b <| i) o
  parLTensor p = wkL p >>> tensorL (negateL (negateL (parL (wkR init) init)))
  parR :: (Neg a, Neg b) => p i (o |> a |> b) -> p i (o |> a ⅋ b)
  parR' :: (Neg a, Neg b) => p i (o |> a ⅋ b) -> p i (o |> a |> b)
  parR' p = exR (wkR (exR (wkR p))) >>> parL (wkR init) init

  tensorL :: (Pos a, Pos b) => p (a <| b <| i) o -> p (a ⊗ b <| i) o
  tensorL = tensorLPar . parR . notR . notR
  tensorLPar :: (Pos a, Pos b) => p i (o |> Not a ⅋ Not b) -> p (a ⊗ b <| i) o
  tensorLPar p = wkL p >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
  tensorL' :: (Pos a, Pos b) => p (a ⊗ b <| i) o -> p (a <| b <| i) o
  tensorL' p = init ⊗ wkL init >>> popL (wkL . wkL . pushL p)
  (⊗) :: (Pos a, Pos b) => p i (o |> a) -> p i (o |> b) -> p i (o |> a ⊗ b)


instance Multiplicative (Seq Δ) where
  botL = popL absurdN
  botR = fmap Left

  oneL = wkL
  oneR = pure (pure One)

  parL a b = popL (exlrI (pushL a) (pushL b))
  parR ab = either (>>= (pure . inlI)) (pure . inrI) <$> ab

  tensorL p = popL (pushL2 p . exlI <*> exrI)
  (⊗) = liftA2 (liftA2 inlrI)


-- Implicative

newtype a --> b = Fun { getFun :: Seq Δ (Negate b <| Γ) (Δ |> Not a) }

infixr 5 -->

instance (Pos a, Neg b) => Polarized N (a --> b) where

appFun' :: (a --> b) -> Seq Δ (Negate b <| i) (o |> Not a)
appFun' = dimap (Γ <$) (first absurdΔ) . getFun


data a --< b = Sub { subA :: !a, subK :: !(Negate b) }

infixr 5 --<

instance (Pos a, Neg b) => Polarized P (a --< b) where


class (Core p, Structural p, Negative p) => Implicative p where
  funL :: (Pos a, Neg b) => p i (o |> a) -> p (b <| i) o -> p (a --> b <| i) o
  funL pa pb = funLSub (subR pa pb)
  funLSub :: (Pos a, Neg b) => p i (o |> a --< b) -> p (a --> b <| i) o
  funLSub p = wkL p >>> subL (exL (funL init init))
  funL2 :: (Pos a, Neg b) => p (a --> b <| a <| i)  (o |> b)
  funL2 = funL init init
  funR :: (Pos a, Neg b) => p (a <| i) (o |> b) -> p i (o |> a --> b)
  funR' :: (Pos a, Neg b) => p i (o |> a --> b) -> p (a <| i) (o |> b)
  funR' p = wkL (exR (wkR p)) >>> funL2

  subL :: (Pos a, Neg b) => p (a <| i) (o |> b) -> p (a --< b <| i) o
  subL = subLFun . funR
  subLFun :: (Pos a, Neg b) => p i (o |> a --> b) -> p (a --< b <| i) o
  subLFun p = wkL p >>> exL (subL (exL (funL init init)))
  subL' :: (Pos a, Neg b) => p (a --< b <| i) o -> p (a <| i) (o |> b)
  subL' p = subR init init >>> wkR (exL (wkL p))
  subR :: (Pos a, Neg b) => p i (o |> a) -> p (b <| i) o -> p i (o |> a --< b)

  ($$) :: (Pos a, Neg b) => p i (o |> a --> b) -> p i (o |> a) -> p i (o |> b)
  f $$ a = exR (wkR f) >>> exR (wkR a) `funL` init


instance Implicative (Seq Δ) where
  funL a b = popL (\ f -> a >>> notR' (exR (negateL' (appFun' f))) >>> exL (wkL b))
  funR b = cont (\ abstract -> Fun (poppedL (poppedR abstract) (notR (exL (negateL b)))))

  subL b = popL (\ s -> pushL b (subA s) >>> pushL (negateL init) (subK s))
  subR a b = liftA2 Sub <$> a <*> negateR b


-- Quantifying

newtype ForAll f = ForAll { runForAll :: forall x . f x }

instance Polarized N (ForAll f)


data Exists f = forall x . Exists (f x)

instance Polarized P (Exists f)

runExists :: (forall x . f x -> r) -> Exists f -> r
runExists f (Exists r) = f r


class (Core p, Structural p, Negative p, Shifting p) => Quantifying p where
  forAllL :: (forall x . Neg (f x)) => p (f x <| i) o -> p (ForAll f <| i) o
  forAllLExists :: (forall x . Neg (f x)) => p i (o |> Exists (Negate · f)) -> p (ForAll f <| i) o
  forAllLExists p = wkL p >>> existsL (mapL getC (negateL (forAllL init)))
  -- FIXME: the correct signature should be p i (o |> (forall x . f x)) -> p i (o |> ForAll f), but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  -- forAllR :: (forall x . Neg (f x)) => (forall x . p i (o |> f x)) -> p i (o |> ForAll f)
  forAllR' :: (forall x . Neg (f x)) => p i (o |> ForAll f) -> (forall x . p i (o |> f x))
  forAllR' p = exR (wkR p) >>> forAllL init

  -- FIXME: the correct signature should be p ((forall x . f x) <| i) o -> p (Exists f <| i) o, but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  existsL :: (forall x . Pos (f x)) => (forall x . p (f x <| i) o) -> p (Exists f <| i) o
  existsL' :: (forall x . Pos (f x)) => p (Exists f <| i) o -> (forall x . p (f x <| i) o)
  existsL' p = existsR init >>> exL (wkL p)
  existsLForAll :: (forall x . Pos (f x)) => p i (o |> ForAll (Not · f)) -> p (Exists f <| i) o
  existsLForAll p = wkL p >>> exL (existsL (exL (forAllL (mapL getC (notL init)))))
  existsR :: p i (o |> f x) -> p i (o |> Exists f)
  existsRForAll :: (forall x . Pos (f x)) => p i (o |> ForAll (Up · f)) -> p i (o |> Exists f)
  existsRForAll = existsR . upR' . mapR getC . forAllR'


instance Quantifying (Seq Δ) where
  forAllL p = mapL runForAll p
  -- forAllR p = mapR ForAll p

  existsL p = popL (runExists (pushL p))
  existsR p = mapR Exists p


-- Recursive

newtype Nu f = Nu { getNu :: Exists (J (J (I :-> f) :⊗ I)) }

instance Polarized N (Nu f) where


newtype Mu f = Mu { getMu :: ForAll (J (J (f :-> I) :-> I)) }

instance Polarized N (Mu f) where


class (Core p, Structural p) => Recursive p where
  nuL :: (forall x . Neg (f x)) => p (Exists (J (J (I :-> f) :⊗ I)) <| i) o -> p (Nu f <| i) o
  nuR :: (forall x . Neg (f x)) => p i (o |> Exists (J (J (I :-> f) :⊗ I))) -> p i (o |> Nu f)

  muL :: (forall x . Pos (f x)) => p (ForAll (J (J (f :-> I) :-> I)) <| i) o -> p (Mu f <| i) o
  muR :: (forall x . Pos (f x)) => p i (o |> ForAll (J (J (f :-> I) :-> I))) -> p i (o |> Mu f)


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
  upL   :: p (a <| i) o -> p (Up   a <| i) o
  upL'   :: p (Up   a <| i) o -> p (a <| i) o
  upL' p = upR init >>> exL (wkL p)
  upR   :: p i (o |> a) -> p i (o |> Up   a)
  upR'   :: p i (o |> Up   a) -> p i (o |> a)
  upR' p = exR (wkR p) >>> upL init

  downL :: p (a <| i) o -> p (Down a <| i) o
  downL'   :: p (Down a <| i) o -> p (a <| i) o
  downL' p = downR init >>> exL (wkL p)
  downR :: p i (o |> a) -> p i (o |> Down a)
  downR'   :: p i (o |> Down a) -> p i (o |> a)
  downR' p = exR (wkR p) >>> downL init


instance Shifting (Seq Δ) where
  upL   = mapL getUp
  upR   = mapR Up

  downL = mapL getDown
  downR = mapR Down


-- Utilities

cont :: ((Seq r i o -> Seq r Γ Δ) -> a) -> Seq Δ i (o |> a)
cont f = Seq $ \ k -> k . Right . f . (`dimap` (k . Left)) . const


newtype I a = I { getI :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Representable) via Identity

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


newtype (f · g) a = C { getC :: f (g a) }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ·

instance (Polarity p, Polarized p (f (g a))) => Polarized p ((f · g) a) where

instance (Applicative f, Applicative g) => Applicative (f · g) where
  pure = C . pure . pure
  f <*> a = C ((<*>) <$> getC f <*> getC a)

instance (Distributive f, Distributive g) => Distributive (f · g) where
  collect f r = C (fmap distribute (collect (getC . f) r))


newtype J p a = J { getJ :: p a a }

instance Bifoldable p => Foldable (J p) where
  foldMap f = bifoldMap f f . getJ

instance Bifunctor p => Functor (J p) where
  fmap f = J . bimap f f . getJ

instance Bitraversable p => Traversable (J p) where
  traverse f = fmap J . bitraverse f f . getJ


newtype (f :-> g) a b = Fn (f a -> g b)

infixr 5 :->


class Conj f g c | c -> f g where
  inlr :: f a -> g b -> a `c` b
  exl :: (a `c` b) -> f a
  exr :: (a `c` b) -> g b

instance Conj I I (,) where
  inlr (I a) (I b) = (a, b)
  exl = I . fst
  exr = I . snd

inlrI :: Conj I I c => a -> b -> (a `c` b)
inlrI a b = inlr (I a) (I b)

exlI :: Conj I I c => (a `c` b) -> a
exlI = getI . exl

exrI :: Conj I I c => (a `c` b) -> b
exrI = getI . exr

foldMapConj :: (Foldable g, Conj f g p, Monoid m) => (b -> m) -> (a `p` b) -> m
foldMapConj f = foldMap f . exr

bifoldMapConj :: (Foldable f, Foldable g, Conj f g p, Monoid m) => (a -> m) -> (b -> m) -> (a `p` b) -> m
bifoldMapConj f g = (<>) <$> foldMap f . exl <*> foldMap g . exr

fmapConj :: (Functor g, Conj f g p) => (b -> b') -> (a `p` b) -> (a `p` b')
fmapConj f = inlr <$> exl <*> fmap f . exr

bimapConj :: (Functor f, Functor g, Conj f g p) => (a -> a') -> (b -> b') -> (a `p` b) -> (a' `p` b')
bimapConj f g = inlr <$> fmap f . exl <*> fmap g . exr

traverseConj :: (Traversable g, Conj f g p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseConj f c = inlr (exl c) <$> traverse f (exr c)

bitraverseConj :: (Traversable f, Traversable g, Conj f g p, Applicative m) => (a -> m a') -> (b -> m b') -> (a `p` b) -> m (a' `p` b')
bitraverseConj f g c = inlr <$> traverse f (exl c) <*> traverse g (exr c)


class Disj f g d | d -> f g where
  inl :: f a -> a `d` b
  inr :: g b -> a `d` b
  exlr :: (f a -> r) -> (g b -> r) -> ((a `d` b) -> r)

instance Disj I I Either where
  inl = Left  . getI
  inr = Right . getI
  exlr f g = either (f . I) (g . I)

inlI :: Disj I I d => a -> a `d` b
inlI = inl . I

inrI :: Disj I I d => b -> a `d` b
inrI = inr . I

exlrI :: Disj I I d => (a -> r) -> (b -> r) -> ((a `d` b) -> r)
exlrI f g = exlr (f . getI) (g . getI)

foldMapDisj :: (Foldable g, Disj f g p, Monoid m) => (b -> m) -> (a `p` b) -> m
foldMapDisj f = exlr (const mempty) (foldMap f)

bifoldMapDisj :: (Foldable f, Foldable g, Disj f g p, Monoid m) => (a -> m) -> (b -> m) -> (a `p` b) -> m
bifoldMapDisj f g = exlr (foldMap f) (foldMap g)

fmapDisj :: (Functor g, Disj f g p) => (b -> b') -> (a `p` b) -> (a `p` b')
fmapDisj f = exlr inl (inr . fmap f)

bimapDisj :: (Functor f, Functor g, Disj f g p) => (a -> a') -> (b -> b') -> (a `p` b) -> (a' `p` b')
bimapDisj f g = exlr (inl . fmap f) (inr . fmap g)

traverseDisj :: (Traversable g, Disj f g p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseDisj f = exlr (pure . inl) (fmap inr . traverse f)

bitraverseDisj :: (Traversable f, Traversable g, Disj f g p, Applicative m) => (a -> m a') -> (b -> m b') -> (a `p` b) -> m (a' `p` b')
bitraverseDisj f g = exlr (fmap inl . traverse f) (fmap inr . traverse g)
